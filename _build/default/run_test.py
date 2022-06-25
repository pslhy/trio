import os
import sys
import subprocess

# args[0] : file
args = sys.argv

# mac은 gtime (brew install gnu-time)
# cmd = "/usr/bin/time -l timeout 10m ./main.sh -max_height 6 -init_comp_size 5 " + args[1]
# cmd = "/usr/bin/time -l timeout 10m ./_build/default/bin/main.exe -max_height 6 -init_comp_size 5 " + args[1]
cmd = "gtime -f 'time(s): %e \nmem(Kb): %M' timeout 10m ./_build/default/bin/main.exe -max_height 6 -init_comp_size 5 " + args[1]
proc = subprocess.run(cmd,capture_output=True, text=True, shell=True)

print("prog : "+args[1])
print(proc.stderr)