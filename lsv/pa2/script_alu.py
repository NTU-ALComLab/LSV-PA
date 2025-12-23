import os
import subprocess
import re

def get_io_counts(abc_binary, file_path):
    """
    先執行一次快速讀取，取得 Input/Output 的數量。
    """
    # 使用 -q -c 讓 ABC 安靜一點，只抓需要的資訊
    cmd = f"read {file_path}; strash; print_stats"
    try:
        process = subprocess.run(
            [abc_binary, "-c", cmd],
            capture_output=True,
            text=True,
            check=True
        )
        output = process.stdout
        
        # Regex 解析: "i/o = <num>/<num>"
        # 例如: "network: i/o = 10/ 2  lat = ..."
        match = re.search(r"i/o\s*=\s*(\d+)\s*/\s*(\d+)", output)
        if match:
            num_inputs = int(match.group(1))
            num_outputs = int(match.group(2))
            return num_inputs, num_outputs
        else:
            print(f"Warning: Could not parse i/o stats for {file_path}")
            return 0, 0
            
    except subprocess.CalledProcessError as e:
        print(f"Error checking stats for {file_path}: {e}")
        return 0, 0

def mainforbdd():
    # --- 設定區 ---
    abc_binary = r"./abc"
    target = r"./lsv/pa1"  # 請確認路徑
    log_path = r"./lsv/pa2/log"
    # -------------
    
    if not os.path.exists(target):
        print(f"Error: Directory {target} does not exist.")
        return

    # 找出所有 .blif 檔案
    benchmarks = [file for file in os.listdir(target) if file.endswith("alu.blif")]
    benchmarks.sort()
    
    os.makedirs(log_path, exist_ok=True)

    for file in benchmarks:
        full_path = os.path.join(target, file)
        file_name, _ = os.path.splitext(file)
        
        # 1. 取得 IO 數量
        num_inputs, num_outputs = get_io_counts(abc_binary, full_path)
        
        if num_inputs == 0 and num_outputs == 0:
            print(f"Skipping {file} (No I/O found or error).")
            continue

        print(f"Running {file} (In: {num_inputs}, Out: {num_outputs})... ", end="", flush=True)

        # 2. 建立指令清單 (Batch Command Construction)
        # 格式: read xxx; strash; lsv 0 0; lsv 0 1; ...
        commands = []
        commands.append(f"read {full_path}")
        commands.append("strash")
        
        for k in range(num_outputs):
            for i in range(num_inputs):
                commands.append(f"lsv_unate_bdd {k} {i}")
        
        # 加入 quit 以確保正常結束
        commands.append("quit")
        
        # 將指令列表合併成一個字串，用換行符號分隔
        full_command_script = "\n".join(commands)

        # 3. 執行 ABC (一次性)
        log_filename = os.path.join(log_path, f"{file_name}_bdd.log")
        
        with open(log_filename, 'w') as log_file:
            # 這裡我們使用 input=full_command_script 將指令「打字」進去
            # 這樣可以避免 Command Line 太長被 OS 拒絕的問題
            try:
                process = subprocess.run(
                    [abc_binary],
                    input=full_command_script,
                    text=True,  # 確保輸入是字串而非 bytes
                    stdout=log_file,
                    stderr=subprocess.STDOUT
                )
                
                if process.returncode != 0:
                    print(f"[FAIL] Return code: {process.returncode}")
                else:
                    print(f"[OK] Log saved to {log_filename}")
                    
            except Exception as e:
                print(f"[ERROR] {e}")

def mainforsat():
    # --- 設定區 ---
    abc_binary = r"./abc"
    target = r"./lsv/pa1"  # 請確認路徑
    log_path = r"./lsv/pa2/log"
    # -------------
    
    if not os.path.exists(target):
        print(f"Error: Directory {target} does not exist.")
        return

    # 找出所有 .blif 檔案
    benchmarks = [file for file in os.listdir(target) if file.endswith("alu.blif")]
    benchmarks.sort()
    
    os.makedirs(log_path, exist_ok=True)

    for file in benchmarks:
        full_path = os.path.join(target, file)
        file_name, _ = os.path.splitext(file)
        
        # 1. 取得 IO 數量
        num_inputs, num_outputs = get_io_counts(abc_binary, full_path)
        
        if num_inputs == 0 and num_outputs == 0:
            print(f"Skipping {file} (No I/O found or error).")
            continue

        print(f"Running {file} (In: {num_inputs}, Out: {num_outputs})... ", end="", flush=True)

        # 2. 建立指令清單 (Batch Command Construction)
        # 格式: read xxx; strash; lsv 0 0; lsv 0 1; ...
        commands = []
        commands.append(f"read {full_path}")
        commands.append("strash")
        
        for k in range(num_outputs):
            for i in range(num_inputs):
                commands.append(f"lsv_unate_sat {k} {i}")
        
        # 加入 quit 以確保正常結束
        commands.append("quit")
        
        # 將指令列表合併成一個字串，用換行符號分隔
        full_command_script = "\n".join(commands)

        # 3. 執行 ABC (一次性)
        log_filename = os.path.join(log_path, f"{file_name}_sat.log")
        
        with open(log_filename, 'w') as log_file:
            # 這裡我們使用 input=full_command_script 將指令「打字」進去
            # 這樣可以避免 Command Line 太長被 OS 拒絕的問題
            try:
                process = subprocess.run(
                    [abc_binary],
                    input=full_command_script,
                    text=True,  # 確保輸入是字串而非 bytes
                    stdout=log_file,
                    stderr=subprocess.STDOUT
                )
                
                if process.returncode != 0:
                    print(f"[FAIL] Return code: {process.returncode}")
                else:
                    print(f"[OK] Log saved to {log_filename}")
                    
            except Exception as e:
                print(f"[ERROR] {e}")

if __name__ == "__main__":
    mainforbdd()
    mainforsat()