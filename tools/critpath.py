#!/usr/bin/env python3
"""The build's critical path, from a `make TIMING=1` run.

Sums each file's sentence times from its `.v.timing` (so process start
is not counted) and walks the `.vo` dependencies in `.Makefile.coq.d`.

Usage (from the repository root):
  tools/critpath.py [-j N] [N_SLOWEST]
  tools/critpath.py --tsv            one row per file: time, finish, slack
  tools/critpath.py --what-if FILE=SECONDS ...
                                     the same report with those files'
                                     times replaced (0 removes a file's
                                     cost), to see what a speedup buys

Prints the total CPU, the critical path with each file's time and finish
time, a simulated wall time at -jN (make starts ready files in
`_CoqProject` order; default -j2), then the N slowest files (`*` marks
those on the path). A file's slack is how much it could slow down
without lengthening the path: speeding up a file with slack does not
shorten a cold build at enough jobs, only CPU.
"""
import argparse
import glob
import re
import signal
import sys


def load(what_if):
    times = {}
    for t in glob.glob('theories/**/*.v.timing', recursive=True):
        tot = 0.0
        for line in open(t, errors='replace'):
            m = re.search(r'\] ([\d.]+) secs', line)
            if m:
                tot += float(m.group(1))
        times[t[:-len('.v.timing')]] = tot
    for kv in what_if:
        f, s = kv.rsplit('=', 1)
        f = re.sub(r'\.v$', '', f)
        times[f] = float(s)
    deps = {}
    for line in open('.Makefile.coq.d'):
        m = re.match(r'(theories/\S+)\.vo .*?: (.*)', line)
        if m:
            deps[m.group(1)] = [d[:-3] for d in m.group(2).split()
                                if d.endswith('.vo')]
    order = []
    for line in open('_CoqProject'):
        line = line.strip()
        if line.endswith('.v'):
            order.append(line[:-2])
    return times, deps, order


def critical(times, deps):
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
    path = []
    while end:
        path.append(end)
        end = pred[end]
    # Latest finish that keeps the build's end: slack.
    rdeps = {}
    for x, ds in deps.items():
        for d in ds:
            rdeps.setdefault(d, []).append(x)
    total = max(fin.values())
    late = {}

    def latest(x):
        if x not in late:
            late[x] = min([latest(r) - times.get(r, 0.0)
                           for r in rdeps.get(x, [])] or [total])
        return late[x]

    slack = {x: latest(x) - fin[x] for x in fin}
    return fin, list(reversed(path)), slack


def simulate(times, deps, order, jobs):
    """Wall time of make -jN, starting ready files in _CoqProject order."""
    rank = {x: i for i, x in enumerate(order)}
    todo = set(deps) | set(order)
    done, running, now = {}, [], 0.0
    while todo or running:
        ready = sorted((x for x in todo
                        if all(d in done for d in deps.get(x, []))),
                       key=lambda x: rank.get(x, len(rank)))
        while ready and len(running) < jobs:
            x = ready.pop(0)
            todo.discard(x)
            running.append((now + times.get(x, 0.0), x))
        if not running:
            break
        running.sort()
        now, x = running.pop(0)
        done[x] = now
    return now


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('n', nargs='?', type=int, default=25)
    ap.add_argument('-j', type=int, default=2)
    ap.add_argument('--tsv', action='store_true')
    ap.add_argument('--what-if', nargs='+', default=[])
    args = ap.parse_args()
    times, deps, order = load(args.what_if)
    if not times:
        sys.exit('no .v.timing files: run `make TIMING=1` first')
    fin, path, slack = critical(times, deps)
    if args.tsv:
        print('#file\tseconds\tfinish\tslack\ton_path')
        for x in sorted(fin, key=fin.get):
            print(f'{x}.v\t{times.get(x, 0):.2f}\t{fin[x]:.2f}\t'
                  f'{slack[x]:.2f}\t{int(x in path)}')
        return
    cpu = sum(times.values())
    print(f"total cpu {cpu:.0f} s, critical path {fin[path[-1]]:.0f} s, "
          f"simulated wall at -j{args.j} {simulate(times, deps, order, args.j):.0f} s "
          f"(-j1 {cpu:.0f}, -j{2 * args.j} "
          f"{simulate(times, deps, order, 2 * args.j):.0f})")
    print("   time   finish  critical path")
    for x in path:
        print(f"  {times.get(x, 0):7.1f}  {fin[x]:7.1f}  {x}")
    print("slowest files (time, slack; * on the path):")
    for x in sorted(times, key=times.get, reverse=True)[:args.n]:
        print(f"  {times[x]:7.1f}  {slack.get(x, 0):7.1f}  "
              f"{'*' if x in path else ' '} {x}")


if __name__ == '__main__':
    signal.signal(signal.SIGPIPE, signal.SIG_DFL)
    main()
