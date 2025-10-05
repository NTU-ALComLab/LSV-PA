#!/usr/bin/env python3
import argparse
import subprocess
import os
import sys

def run_abc_command(abc_path, blif_file, command):
    """Run ABC with the given command on a BLIF file and return the output."""
    try:
        # Construct ABC commands
        abc_commands = f"read {blif_file}; strash; {command}"
        
        # Run ABC
        proc = subprocess.run([abc_path], 
                            input=abc_commands, 
                            text=True, 
                            capture_output=True, 
                            timeout=30)
        
        if proc.returncode != 0:
            print(f"Error running ABC: {proc.stderr}")
            return None
            
        # Extract the command output (skip ABC header/footer)
        lines = proc.stdout.strip().split('\n')
        output_lines = []
        in_output = False
        
        for line in lines:
            if command in line:
                in_output = True
                continue
            elif line.startswith('abc ') and '>' in line:
                if in_output:
                    break
            elif in_output and line.strip():
                output_lines.append(line.strip())
        
        return '\n'.join(output_lines)
        
    except Exception as e:
        print(f"Exception running ABC: {e}")
        return None

def normalize_output(output):
    """Normalize output for comparison (sort lines, remove empty lines)."""
    if not output:
        return ""
    lines = [line.strip() for line in output.split('\n') if line.strip()]
    return '\n'.join(sorted(lines))

def main():
    parser = argparse.ArgumentParser(description='Check LSV PA1 implementations')
    parser.add_argument('--abc', required=True, help='Path to ABC executable')
    parser.add_argument('--cmd1', required=True, help='First command to test')
    parser.add_argument('--cmd2', required=True, help='Second command to test')
    parser.add_argument('--paths', required=True, help='Path to BLIF file or directory')
    parser.add_argument('--k', type=int, default=4, help='k parameter (default: 4)')
    parser.add_argument('--l', type=int, default=2, help='l parameter (default: 2)')
    
    args = parser.parse_args()
    
    # Build full command strings
    cmd1_full = f"{args.cmd1} {args.k} {args.l}"
    cmd2_full = f"{args.cmd2} {args.k} {args.l}"
    
    # Get list of files to test
    if os.path.isdir(args.paths):
        blif_files = [os.path.join(args.paths, f) for f in os.listdir(args.paths) if f.endswith('.blif')]
    else:
        blif_files = [args.paths]
    
    total_tests = 0
    passed_tests = 0
    
    for blif_file in blif_files:
        if not os.path.exists(blif_file):
            print(f"File not found: {blif_file}")
            continue
            
        print(f"Testing: {blif_file}")
        
        # Run both commands
        output1 = run_abc_command(args.abc, blif_file, cmd1_full)
        output2 = run_abc_command(args.abc, blif_file, cmd2_full)
        
        if output1 is None or output2 is None:
            print(f"  FAILED: Could not run commands")
            total_tests += 1
            continue
        
        # Normalize and compare outputs
        norm_output1 = normalize_output(output1)
        norm_output2 = normalize_output(output2)
        
        total_tests += 1
        if norm_output1 == norm_output2:
            print(f"  PASSED")
            passed_tests += 1
        else:
            print(f"  FAILED: Outputs differ")
            print(f"    {args.cmd1} output:")
            for line in norm_output1.split('\n'):
                print(f"      {line}")
            print(f"    {args.cmd2} output:")
            for line in norm_output2.split('\n'):
                print(f"      {line}")
    
    print(f"\nResults: {passed_tests}/{total_tests} tests passed")
    return 0 if passed_tests == total_tests else 1

if __name__ == '__main__':
    sys.exit(main())