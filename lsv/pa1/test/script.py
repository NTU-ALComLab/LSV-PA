import os
import subprocess

def main():
  target = r"./lsv/pa1/benchmarks"
  log_path = r"./log"
  benchmarks = [file for file in os.listdir(target) if os.path.splitext(file)[1] == ".blif"]
  benchmarks.sort()
  os.makedirs(log_path, exist_ok=True)

  crashed = 0
  for file in benchmarks:
    file_name, _ = os.path.splitext(file)
    for k in range(3, 7):
      for l in range(1, 5):
        print(f"Running benchmark {file}, k = {k}, l = {l}", flush=True)
        with open(os.path.join(log_path, f"{file_name}_k{k}_l{l}.log"), 'w') as log_file:
          returncode = subprocess.run(
              [r"./abc", "-q",
               f"read {os.path.join(target, file)}; st; lsv_printmocut {k} {l}"],
              stdout=log_file, stderr=subprocess.STDOUT).returncode
          if returncode != 0:
            crashed += 1
            print(f"abc crashed with return code {returncode}")
  if crashed != 0:
    print(f"Number of crashed runs: {crashed}")
  else:
    print("All runs finished without crashing")

if __name__ == "__main__":
  main()
