import os
import sys
import time
import subprocess

# python3 new_test.py
# python3 new_test.py testcases/new

# args[0] : dir name
args = sys.argv
# print(len(sys.argv))
# print(args[0])
if len(sys.argv) > 1 :
    target_dir=args[1]
    print(target_dir)
    for file in os.listdir(target_dir):
        print(file)
        cmd = "python3 ./run_test.py " + target_dir+"/"+file
        proc = subprocess.run(cmd,capture_output=True, text=True, shell=True)
        print(proc.stdout)
    
else:
    f = open('list', 'r')
    lists = f.readlines()
    for file in lists:
        cmd = "python3 ./run_test.py " + file
        proc = subprocess.run(cmd,capture_output=True, text=True, shell=True)
        print(proc.stdout)