#!/usr/bin/env python3
import argparse, os, re, subprocess, sys, tempfile
from pathlib import Path
# 放在檔頭 imports 底下
from concurrent.futures import ProcessPoolExecutor, as_completed
import multiprocessing

def task(args_pack):
    abc_bin, blif, cmd1, cmd2, k, l, timeout = args_pack
    base = Path(blif).stem
    out_dir = Path("output_logs") / base
    try:
        out1 = run_abc(abc_bin, Path(blif), cmd1, k, l, timeout=timeout)
    except subprocess.TimeoutExpired:
        out1 = f"[TIMEOUT] {cmd1} k={k} l={l}"
    except Exception as e:
        out1 = f"[ERROR] {cmd1} k={k} l={l}: {e}"

    try:
        out2 = run_abc(abc_bin, Path(blif), cmd2, k, l, timeout=timeout)
    except subprocess.TimeoutExpired:
        out2 = f"[TIMEOUT] {cmd2} k={k} l={l}"
    except Exception as e:
        out2 = f"[ERROR] {cmd2} k={k} l={l}: {e}"
    # 寫檔（彼此不會衝突，因為檔名包含 k,l 與 1/2）
    write_text(out_dir / f"k{k}l{l}1.txt", out1)
    write_text(out_dir / f"k{k}l{l}2.txt", out2)
    set1 = parse_cuts(out1)
    set2 = parse_cuts(out2)
    write_text(out_dir / f"k{k}l{l}1.norm.txt", "\n".join(sorted(set1)) + ("\n" if set1 else ""))
    write_text(out_dir / f"k{k}l{l}2.norm.txt", "\n".join(sorted(set2)) + ("\n" if set2 else ""))
    only1 = set1 - set2
    only2 = set2 - set1
    # 回傳讓主行程印
    # 多回傳兩個旗標，讓主程式明確知道是不是 timeout / error
    return (blif, k, l, only1, only2, out1, out2,
            "[TIMEOUT]" in out1 or "[TIMEOUT]" in out2,
            out1.startswith("[ERROR]") or out2.startswith("[ERROR]"))

# ---------- parse & normalize "inputs : outputs" lines ----------
CUT_RX = re.compile(r"^\s*([^\s].*?)\s*:\s*([^\s].*?)\s*$")

def _normalize_side(tokens):
    ints, all_int = [], True
    for t in tokens:
        try: ints.append(int(t))
        except ValueError: all_int = False; break
    if all_int:
        ints.sort()
        return " ".join(str(x) for x in ints)
    return " ".join(sorted(tokens))

def parse_cuts(stdout: str):
    cuts = set()
    for raw in stdout.splitlines():
        line = raw.strip()
        if (not line or line.startswith("*")
            or "cmd error" in line.lower()
            or "abc command line" in line.lower()
            or line.lower().startswith("usage:")
            or line.endswith(">")):
            continue
        m = CUT_RX.match(line)
        if not m: continue
        L = _normalize_side(m.group(1).split())
        R = _normalize_side(m.group(2).split())
        if L and R:
            cuts.add(f"{L} : {R}")
    return cuts

# ---------- utils ----------
def write_text(path: Path, text: str):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)

def print_diff(title: str, only_a: set, only_b: set, out=sys.stdout):
    print(title, file=out)
    if not only_a and not only_b:
        print("  ✓ identical", file=out); return
    if only_a:
        print("  present only in cmd1:", file=out)
        for s in sorted(only_a): print("    " + s, file=out)
    if only_b:
        print("  present only in cmd2:", file=out)
        for s in sorted(only_b): print("    " + s, file=out)

def collect_blifs(paths):
    files = []
    for p in paths:
        P = Path(p)
        if P.is_dir(): files += sorted(P.rglob("*.blif"))
        elif P.is_file() and P.suffix.lower()==".blif": files.append(P)
        else: print(f"[warn] skip: {p}", file=sys.stderr)
    return files

# ---------- ABC runner (temp script, not saved) ----------
def run_abc(abc_bin: str, blif_path: Path, cmd: str, k: int, l: int, timeout=None) -> str:
    # Require single-token command names
    if re.search(r"\s", cmd):
        raise ValueError(f"command '{cmd}' contains whitespace")

    script = f'read "{str(blif_path)}"\nstrash\n{cmd} {k} {l}\n'
    with tempfile.NamedTemporaryFile("w", delete=False, suffix=".abc") as tf:
        tf.write(script)
        script_path = tf.name
    try:
        proc = subprocess.run(
            [abc_bin, "-f", script_path],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=timeout,
            check=False,
        )
        return proc.stdout
    finally:
        try: os.unlink(script_path)
        except OSError: pass

# ---------- CLI ----------
def main():
    ap = argparse.ArgumentParser(description="Compare outputs of two ABC KL-cut commands on BLIFs.")
    ap.add_argument("--abc", default="../../abc", help="Path to abc binary")
    ap.add_argument("--cmd1", default="lsv_printmocut", help="First command (single token)")
    ap.add_argument("--cmd2", default="lsv_printmocut_2", help="Second command (single token)")
    # Defaults: all 24 combos
    ap.add_argument("--k", type=int, nargs="*", default=[3,4,5,6], help="k values (default: 3 4 5 6)")
    ap.add_argument("--l", type=int, nargs="*", default=[1,2,3,4], help="l values (default: 1 2 3 4)")
    ap.add_argument("--timeout", type=int, default=60, help="ABC timeout (s)")
    ap.add_argument("--paths", nargs="+", help="BLIF files or directories")
    ap.add_argument("--jobs", "-j", type=int, default=max(1, multiprocessing.cpu_count() // 2),
                    help="Parallel workers (default: ~half of CPUs)")
    args = ap.parse_args()

    blifs = collect_blifs(args.paths)
    if not blifs:
        print("No BLIF inputs found.", file=sys.stderr); sys.exit(2)
    
    # 建立任務列表
    jobs = []
    for blif in blifs:
        for k in args.k:
            for l in args.l:
                jobs.append((args.abc, str(blif), args.cmd1, args.cmd2, k, l, args.timeout))

    ok_all = True
    # 平行跑
    with ProcessPoolExecutor(max_workers=args.jobs) as ex:
        futures = [ex.submit(task, pack) for pack in jobs]
        for fut in as_completed(futures):
            blif, k, l, only1, only2, out1, out2, timedout, errored = fut.result()
            print(f"\n=== {blif} ===\n-- k={k} l={l}")
            if timedout:
                print("  compare: (skipped) timeout occurred")
            elif errored:
                print("  compare: (skipped) error occurred")
            else:
                print_diff("  compare:", only1, only2)

            if timedout or errored or only1 or only2 \
            or "unknown command" in out1.lower() or "unknown command" in out2.lower():
                ok_all = False

    sys.exit(0 if ok_all else 1)

if __name__ == "__main__":
    main()
