import sys

# args[1] : log name
args = sys.argv
file = args[1]

f = open(file)
# f.close()
s = ""
data = f.readlines()
# print(data)
out = open('log/output.csv','w')
for line in data :
    # print(line)
    if "prog : " in line:
        s += (line.strip("prog : ").strip() + ",")
    if "Size: " in line:
        s += (line.strip("Size: ").strip() + ",")
    if "Iter: " in line:
        s += (line.strip("Iter: ").strip() + ",")
    if "Time(s): " in line:
        s += (line.strip("Time(s): ").strip() + ",")
    if "Mem(Kb): " in line:
        # print(s)
        s += (line.strip("Mem(Kb): ").strip() + "\n")
        # print(s)
        out.write(s)
        s = ""
f.close()
out.close()