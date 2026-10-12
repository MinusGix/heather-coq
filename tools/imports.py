#!/usr/bin/env python3
"""Imports that hold a file back: what it requires against what it uses.

A file starts building only once everything it (transitively) requires
is built. This compares, for each file, the finish time of its
dependencies (from `.Makefile.coq.d` and the `.v.timing` files of a
`make TIMING=1` build, as in tools/critpath.py) with the finish time of
the modules it actually *references*, read from its `.glob` file. A big
gap means the file waits for modules it never names: requiring a lower
module could let it start earlier (and, on the critical path, shorten
the build).

Usage (from the repository root, after `make TIMING=1`):
  tools/imports.py [-n N] [FILE.v ...]   files with the largest gaps
  tools/imports.py --path                only the files on the critical path

The `.glob` lists constants, inductives and notations a file uses, but not
tactics, hints, instances found by resolution or `Ltac` from another
file, so a gap is a candidate to check by compiling, not a proof.
"""
import argparse
import os
import re
import signal
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from critpath import load, critical  # noqa: E402


def module_of(path):
    return 'DeLaM.' + path[len('theories/'):].replace('/', '.')


def refs(path):
    used = set()
    try:
        for line in open(path + '.glob', errors='replace'):
            if line.startswith('R'):
                parts = line.split()
                # (`lib` is the `Require` itself, not a use)
                if len(parts) > 4 and parts[1].startswith('DeLaM.') \
                        and parts[4] != 'lib':
                    used.add(parts[1])
    except OSError:
        pass
    return used


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('files', nargs='*')
    ap.add_argument('-n', type=int, default=25)
    ap.add_argument('--path', action='store_true')
    args = ap.parse_args()
    times, deps, order = load([])
    fin, path, slack = critical(times, deps)
    by_mod = {module_of(x): x for x in fin}
    rows = []
    targets = [re.sub(r'\.v$', '', f) for f in args.files] or \
        (path if args.path else list(fin))
    for x in targets:
        ds = deps.get(x, [])
        start = max((fin[d] for d in ds), default=0.0)
        used = [by_mod[m] for m in refs(x) if m in by_mod and by_mod[m] != x]
        need = max((fin[u] for u in used), default=0.0)
        last = max(used, key=lambda u: fin[u], default=None)
        waits = max(ds, key=lambda d: fin[d], default=None)
        rows.append((start - need, x, start, need, waits, last))
    rows.sort(reverse=True)
    print('     gap    start  needed  file  (waits for -> latest it uses)')
    for gap, x, start, need, waits, last in rows[:args.n]:
        on = '*' if x in path else ' '
        print(f'{gap:8.1f} {start:8.1f} {need:7.1f} {on}{x}  ({waits} -> {last})')


if __name__ == '__main__':
    signal.signal(signal.SIGPIPE, signal.SIG_DFL)
    main()
