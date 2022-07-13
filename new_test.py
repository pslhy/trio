import os
import sys
import time
import subprocess


# python3 new_test.py trio testcases/new
# python3 new_test.py trio testcases basic_list

# args[1] : synthesizer 
# args[2] : dir name

args = sys.argv
synth = args[1]
# print((sys.argv))
# print(args[0])

if len(sys.argv) < 4 :
    target_dir=args[2]
    print(target_dir)
    for file in os.listdir(target_dir):
        print(file)
        cmd = "python3 ./run_test.py " + synth + " " + target_dir+"/"+file
        proc = subprocess.run(cmd,capture_output=True, text=True, shell=True)
        print(proc.stdout)
    
else:
    tlist = args[3]
    target_dir=args[2]
    f = open(tlist, 'r')
    lists = f.readlines()
    for file in lists:
        cmd = "python3 ./run_test.py " + synth + " " + target_dir + "/" + file
        proc = subprocess.run(cmd,capture_output=True, text=True, shell=True)
        print(proc.stdout)