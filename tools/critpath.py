#!/usr/bin/env python3
"""The build's critical path, from a `make TIMING=1` run.

Sums each file's sentence times from its `.v.timing` (so library loading is
not counted) and walks the `.vo` dependencies in `.Makefile.coq.d`.

Usage: tools/critpath.py [N]   (from the repository root; N slowest files)

Prints the total CPU, the critical path with each file's time and finish
time, then the N slowest files (`*` marks those on the path). With `-j2`,
the wall time is about the critical path plus loading, as long as the total
CPU stays under twice the path.
"""
import glob
import os
import re
import sys

times = {}
for t in glob.glob('theories/**/*.v.timing', recursive=True):
    tot = 0.0
    for line in open(t):
        m = re.search(r'\] ([\d.]+) secs', line)
        if m:
            tot += float(m.group(1))
    times[t[:-len('.v.timing')]] = tot

deps = {}
for line in open('.Makefile.coq.d'):
    m = re.match(r'(theories/\S+)\.vo .*?: (.*)', line)
    if m:
        deps[m.group(1)] = [d[:-3] for d in m.group(2).split() if d.endswith('.vo')]

fin, pred = {}, {}
def finish(x):
    if x not in fin:
        best, bp = 0.0, None
        for d in deps.get(x, []):
            if finish(d) > best:
                best, bp = finish(d), d
        fin[x], pred[x] = best + times.get(x, 0.0), bp
    return fin[x]

for x in deps:
    finish(x)
end = max(fin, key=fin.get)
print(f"total cpu {sum(times.values()):.0f} s, critical path {fin[end]:.0f} s")
path = []
while end:
    path.append(end)
    end = pred[end]
for x in reversed(path):
    print(f"  {times.get(x, 0):7.1f}  {fin[x]:7.1f}  {x}")
n = int(sys.argv[1]) if len(sys.argv) > 1 else 25
print("slowest files:")
for x in sorted(times, key=times.get, reverse=True)[:n]:
    print(f"  {times[x]:7.1f}  {'*' if x in path else ' '} {x}")
