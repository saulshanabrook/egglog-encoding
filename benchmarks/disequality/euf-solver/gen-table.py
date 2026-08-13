import sys

if len(sys.argv) != 2:
    print("USAGE: python3 %s csv_file" % sys.argv[0])
    exit(-1)

result_file = sys.argv[1]

# CSV columns
METHOD                   = 0
FILENAME                 = 1
STATUS                   = 2
EGRAPH_SETUP_TIME        = 3
FULL_TIME                = 4
SAT_SOLUTION_ITER_NUMBER = 5
NUM_NODES                = 6
NUM_CLASSES              = 7
SAT_TIME                 = 8
EGRAPH_TIME              = 9

# A utility function that returns a lambda that projects a row to a particular cell and applies
# a given formatter to it
def proj(header, formatter):
    return lambda cells: formatter(cells[header])


# A utility function that converts durations with human-readable units to a floating number in
# seconds
def hrtime2sec(time):
    if time.endswith("ms"): return float(time[:-2]) * 1e-3
    if time.endswith("µs"): return float(time[:-3]) * 1e-6
    if time.endswith("ns"): return float(time[:-2]) * 1e-9
    if time.endswith("s"):  return float(time[:-1])
    assert False, "Unknown unit while converting " + time


# a dictionary that maps filenames (strings) to another dictionary with two keys: 'ee' and 'de'.
# both keys point to a list of relevant lines (split into cells) in the CSV file
results_by_file = {}

for line in open(result_file).readlines():
    line = line[:-1] # remove new line at the end

    if len(line) == 0: continue # ignore empty lines
    if line.startswith("method,"): continue # ignore CSV header lines

    cells = line.split(',')

    if cells[FILENAME] not in results_by_file:
        results_by_file[cells[FILENAME]] = { 'de': [], 'ee': [] }

    results_by_file[cells[FILENAME]][cells[METHOD]].append(cells)

# Since DE is (almost always) faster than EE, there will be more files accepted by DE, thus there
# will be some files that we can't find the ratio for.
# In the following we analyze only those files which we have data for.

count_files = 0
sum_ratio_nodes = 0.0
sum_ratio_classes = 0.0
sum_ratio_time = 0.0

for filename in results_by_file:
    ee = results_by_file[filename]['ee']
    de = results_by_file[filename]['de']

    # ignore exactly those files which we don't have data about from both approaches
    if len(ee) == 0 or len(de) == 0: continue

    # for a very few cases, the number of iterations the SAT solver has to cycle through is
    # different for both approaches. One reason is the timeout. We ignore these cases since
    # otherwise the magnitudes won't match
    if len(ee) != len(de): continue

    count_files += 1
    sum_ratio_nodes += sum(map(proj(NUM_NODES, int), de))                                          \
                     / sum(map(proj(NUM_NODES, int), ee))

    sum_ratio_classes += sum(map(proj(NUM_CLASSES, int), de))                                      \
                       / sum(map(proj(NUM_CLASSES, int), ee))

    # The full time is the same across all SAT iterations, afterall it *is* the full time to check
    # sat/unsat which has to cycle through all solutions!
    sum_ratio_time += proj(FULL_TIME, hrtime2sec)(de[0])                                           \
                    / proj(FULL_TIME, hrtime2sec)(ee[0])


print("Average Ratio DE/EE of E-Nodes: %f" % (sum_ratio_nodes / count_files))
print("Average Ratio DE/EE of E-Classes: %f" % (sum_ratio_classes / count_files))
print("Average Ratio DE/EE of Time: %f" % (sum_ratio_time / count_files))
