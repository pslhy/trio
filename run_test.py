import os
import sys
import subprocess
from telnetlib import theNULL

# args[1] : option
# args[2] : file
args = sys.argv
file = args[2]
synth = args[1]
print("synthesizer :" + synth)
if synth == "trio" :
    cmd = "gtime -f 'Time(s): %e \nMem(Kb): %M' timeout 2m _build/default/bin/main.exe " + file
    proc = subprocess.run(cmd,capture_output=True, text=True, shell=True)

    print("prog : "+file)
    print(proc.stdout)
    print(proc.stderr)

elif synth == "noinvmap" :
    cmd = "gtime -f 'Time(s): %e \nMem(Kb): %M' timeout 2m _build/default/bin/main.exe -noinvmap " + file
    proc = subprocess.run(cmd,capture_output=True, text=True, shell=True)

    print("prog : "+file)
    print(proc.stdout)
    print(proc.stderr)

elif synth == "nofilter" :
    cmd = "gtime -f 'Time(s): %e \nMem(Kb): %M' timeout 2m _build/default/bin/main.exe -nofilter " + file
    proc = subprocess.run(cmd,capture_output=True, text=True, shell=True)

    print("prog : "+file)
    print(proc.stdout)
    print(proc.stderr)

elif synth == "noinvfilter" :
    cmd = "gtime -f 'Time(s): %e \nMem(Kb): %M' timeout 2m _build/default/bin/main.exe -noinvmap -nofilter " + file
    proc = subprocess.run(cmd,capture_output=True, text=True, shell=True)

    print("prog : "+file)
    print(proc.stdout)
    print(proc.stderr)

else : print("invalid synthesizer !")

# mac은 gtime (brew install gnu-time)
# cmd = "/usr/bin/time -l timeout 10m ./main.sh -max_height 6 -init_comp_size 5 " + args[1]
# cmd = "/usr/bin/time -l timeout 10m ./_build/default/bin/main.exe -max_height 6 -init_comp_size 5 " + args[1]
# cmd = "gtime -f 'time(s): %e \nmem(Kb): %M' timeout 10m ./_build/default/bin/main.exe -max_height 6 -init_comp_size 5 " + args[1]
# proc = subprocess.run(cmd,capture_output=True, text=True, shell=True)

# print("prog : "+args[1])
# print(proc.stderr)
