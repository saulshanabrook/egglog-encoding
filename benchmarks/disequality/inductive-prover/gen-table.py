import sys

if len(sys.argv) != 2:
    print("USAGE: python3 %s csv_file" % sys.argv[0])
    exit(-1)

results_file = sys.argv[1]

# Utility function that converts strings representing time as produced by the `time` command to
# a float number in seconds
def hrtime2sec(s):
    [minutes, seconds] = s[:-1].split('m')
    return float(minutes)*60 + float(seconds)

count_files = 0
sum_ratio_nodes = 0.0
sum_ratio_classes = 0.0
sum_ratio_time = 0.0

for line in open(results_file).readlines():
    if line.startswith("file,"): continue # ignore header line

    line = line[:-1]

    [filename, num_classes_ee, num_nodes_ee, time_ee, num_classes_de, num_nodes_de, time_de] = line.split(',')

    try:
        count_files += 1
        sum_ratio_nodes += float(num_nodes_de) / float(num_nodes_ee)
        sum_ratio_classes += float(num_classes_de) / float(num_classes_ee)
        sum_ratio_time += hrtime2sec(time_de) / hrtime2sec(time_ee)
    except Exception: continue # happens when a files times out

print("Average Ratio DE/EE of E-Nodes: %f" % (sum_ratio_nodes / count_files))
print("Average Ratio DE/EE of E-Classes: %f" % (sum_ratio_classes / count_files))
print("Average Ratio DE/EE of Time: %f" % (sum_ratio_time / count_files))
