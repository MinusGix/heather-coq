#!/usr/bin/env python3
"""What the dependency graph could be: files and declarations by what they use.

A file starts building once everything it requires is built, but it may
use only part of that, and only some of its own declarations may need
the latest of it. This reads the `.glob` files (which constants,
inductives and notations each sentence references, at byte positions)
and the `.v.timing` files of a `make TIMING=1` build (the time of each
sentence, at the same byte positions), as tools/critpath.py does, and
answers two questions:

  tools/depgraph.py --ideal [-j N] [N_SLOWEST]
      The critical path if every file required only the modules it
      references: a lower bound for reordering the `Require`s without
      splitting files, and the files whose place in the chain is only
      an artifact of the `Require` order (`moved` in the report).

  tools/depgraph.py FILE.v [--ideal] [--decls]
      FILE's declarations grouped by the latest module each needs
      (directly or through earlier declarations of FILE), with the time
      of each group: the parts of FILE that could move to a file of
      their own that starts earlier. `--ideal` measures "earlier"
      against the reference graph instead of the actual one; `--decls`
      lists every declaration with its time, the longest chain ending in
      it and the latest module it needs (what to move where).

The `.glob` does not record tactics (`Ltac`), hints, instances found by
resolution or `Ltac2` used across files, so a reference graph can be
too optimistic: treat its answers as candidates to check by compiling.
"""
import argparse
import os
import re
import signal
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from critpath import load, critical, simulate  # noqa: E402

TACTIC = re.compile(r'(#\[[^]]*\] *)?((Local|Global|Export) +)?'
                    r'(Ltac|Hint|Tactic Notation|Create HintDb|Opaque|'
                    r'Transparent|Arguments|Existing)\b')
SKIP_KINDS = {'binder', 'var', 'sec', 'mod', 'modtype', 'lib'}


def module_of(path):
    return 'DeLaM.' + path[len('theories/'):].replace('/', '.')


def read_glob(path):
    """Definitions [(pos, name)] and references [(pos, module, name)]."""
    defs, refs = [], []
    try:
        lines = open(path + '.glob', errors='replace').read().split('\n')
    except OSError:
        return defs, refs
    for line in lines:
        m = re.match(r'R(\d+):\d+ (\S+) (\S+) (\S+) (\S+)', line)
        if m:
            if m.group(5) not in SKIP_KINDS:
                refs.append((int(m.group(1)), m.group(2), m.group(4)))
            continue
        m = re.match(r'(\w+) (\d+):\d+ (\S+) (\S+)', line)
        if m and m.group(1) not in SKIP_KINDS:
            defs.append((int(m.group(2)), m.group(4)))
    return defs, refs


def read_timing(path):
    sents = []
    try:
        for line in open(path + '.v.timing', errors='replace'):
            m = re.match(r'Chars (\d+) - (\d+) \[(.*)\] ([\d.]+) secs', line)
            if m:
                sents.append((int(m.group(1)), int(m.group(2)),
                              m.group(3).replace('~', ' '),
                              float(m.group(4))))
    except OSError:
        pass
    return sents


def referenced(x, by_mod):
    _, refs = read_glob(x)
    me = module_of(x)
    return sorted({by_mod[m] for _, m, _ in refs
                   if m in by_mod and m != me})


def ideal_deps(deps):
    by_mod = {module_of(x): x for x in deps}
    return {x: referenced(x, by_mod) for x in deps}


def report_ideal(times, deps, order, jobs, n):
    ideal = ideal_deps(deps)
    fin, path, _ = critical(times, deps)
    ifin, ipath, _ = critical(times, ideal)
    print(f'actual: critical path {max(fin.values()):.0f} s, '
          f'simulated -j{jobs} {simulate(times, deps, order, jobs):.0f} s')
    print(f'ideal:  critical path {max(ifin.values()):.0f} s, '
          f'simulated -j{jobs} {simulate(times, ideal, order, jobs):.0f} s'
          '  (each file requiring only what it references)')
    print('   time   finish  actual  ideal critical path')
    for x in ipath:
        print(f'{times.get(x, 0):7.1f} {ifin[x]:8.1f} {fin[x]:7.1f}  {x}')
    print('files that would start earliest, relative to now '
          '(actual start - ideal start):')
    rows = []
    for x in fin:
        a = fin[x] - times.get(x, 0)
        i = ifin[x] - times.get(x, 0)
        rows.append((a - i, x, a, i))
    rows.sort(reverse=True)
    for d, x, a, i in rows[:n]:
        on = '*' if x in path else ' '
        print(f'{d:8.1f} moved {a:7.1f} -> {i:7.1f} {on}{x}  '
              f'(uses {", ".join(y.split("/")[-1] for y in ideal[x][-3:])})')


def report_file(f, times, deps, ideal, listing=False):
    x = re.sub(r'\.v$', '', f)
    graph = ideal_deps(deps) if ideal else deps
    fin, _, _ = critical(times, graph)
    by_mod = {module_of(y): y for y in deps}
    me = module_of(x)
    defs, refs = read_glob(x)
    sents = read_timing(x)
    if not sents:
        sys.exit(f'no timing for {x}: build with make TIMING=1 first')
    # Declarations start at the sentence holding their name.
    starts = []
    for pos, name in sorted(defs):
        for i, (a, b, _, _) in enumerate(sents):
            if a <= pos <= b:
                if not starts or starts[-1][0] != i:
                    starts.append((i, name, []))
                else:
                    starts[-1][2].append(name)
                break
    # Tactics and hints are invisible to the `.glob`: every declaration
    # after one is taken to use it (and so to need what it references).
    taken = {i for i, _, _ in starts}
    for i, (_, _, text, _) in enumerate(sents):
        if i not in taken and TACTIC.match(text):
            starts.append((i, '[' + ' '.join(text.split()[:3]) + ']', []))
    starts.sort(key=lambda s: s[0])
    decls = []
    first = starts[0][0] if starts else len(sents)
    head = sum(s[3] for s in sents[:first])
    for k, (i, name, also) in enumerate(starts):
        j = starts[k + 1][0] if k + 1 < len(starts) else len(sents)
        a, b = sents[i][0], sents[j - 1][1] if j > i else sents[i][1]
        t = sum(s[3] for s in sents[i:j])
        decls.append({'tactic': name.startswith('['), 'name': name, 'names': [name] + also, 'a': a,
                      'b': b, 't': t, 'line': sents[i][2][:50]})
    owner = {}
    for d in decls:
        for nm in d['names']:
            owner[nm] = d
    tactics = []
    for d in decls:
        ext, internal = set(), set()
        for pos, mod, name in refs:
            if d['a'] <= pos <= d['b']:
                if mod == me:
                    o = owner.get(name) or owner.get(name.split('.')[-1])
                    if o is not None and o is not d and o['a'] < d['a']:
                        internal.add(id(o))
                elif mod in by_mod:
                    ext.add(by_mod[mod])
        internal |= {id(o) for o in tactics}
        d['ext'], d['int'] = ext, internal
        if d['tactic']:
            tactics.append(d)
    byid = {id(d): d for d in decls}
    for d in decls:
        need = max(d['ext'], key=lambda y: fin[y], default=None)
        for i in d['int']:
            o = byid[i]
            if o['need'] is not None and (
                    need is None or fin[o['need']] > fin[need]):
                need = o['need']
        d['need'] = need
    start = max((fin[y] for y in graph.get(x, [])), default=0.0)
    print(f'{x}: {sum(d["t"] for d in decls) + head:.1f} s '
          f'in {len(decls)} declarations, starts at {start:.1f} s '
          f'({"reference" if ideal else "actual"} graph)')
    groups = {}
    for d in decls:
        groups.setdefault(d['need'], []).append(d)
    print('   time  ready-at  decls  latest module needed  (slowest)')
    for need in sorted(groups, key=lambda y: fin[y] if y else 0.0):
        ds = groups[need]
        t = sum(d['t'] for d in ds)
        slow = max(ds, key=lambda d: d['t'])
        ready = fin[need] if need else 0.0
        print(f'{t:7.1f} {ready:9.1f} {len(ds):6d}  {need}  '
              f'({slow["name"]} {slow["t"]:.1f} s)')
    # The longest chain of declarations using one another: what is left
    # of the file's time if its independent parts built in parallel.
    for d in decls:
        best = max((byid[i] for i in d['int']), key=lambda o: o['chain'],
                   default=None)
        d['chain'] = d['t'] + (best['chain'] if best else 0.0)
        d['prev'] = best
    end = max(decls, key=lambda d: d['chain'], default=None)
    if end:
        chain = []
        while end:
            chain.append(end)
            end = end['prev']
        print(f'longest chain of declarations using one another: '
              f'{chain[0]["chain"]:.1f} s')
        for d in reversed(chain):
            if d['t'] >= 0.5:
                print(f'{d["t"]:7.1f}  {d["name"]}')
    if listing:
        print('every declaration: time, chain ending in it, latest module '
              'needed, line')
        for d in decls:
            need = d['need'].split('/')[-1] if d['need'] else '-'
            print(f'{d["t"]:7.2f} {d["chain"]:7.2f}  {need:22s} {d["line"]}')


def resolve(name, files):
    name = re.sub(r'\.v$', '', name)
    hits = [x for x in files if x == name or x.endswith('/' + name)]
    if len(hits) != 1:
        sys.exit(f'{name}: matches {hits or "no file"}')
    return hits[0]


def closure(graph, xs):
    seen, todo = set(), list(xs)
    while todo:
        y = todo.pop()
        if y not in seen:
            seen.add(y)
            todo.extend(graph.get(y, []))
    return seen


def report_try(edits, times, deps, order, jobs, n):
    """Replace files' `Require`s, add what their users then miss, report."""
    files = list(deps)
    refs = ideal_deps(deps)
    new = {x: list(ds) for x, ds in deps.items()}
    for e in edits:
        x, mods = e.split('=', 1)
        x = resolve(x, files)
        if mods == '@':
            # only what it references, without what those already export
            r = refs[x]
            new[x] = [m for m in r
                      if not any(m in closure(deps, deps[o])
                                 for o in r if o != m)]
        else:
            new[x] = [resolve(m, files) for m in mods.split(',') if m]
        print(f'{x}: requires {", ".join(new[x]) or "nothing"} '
              f'(was {", ".join(deps[x])})')
    # A file that used a module through an edited file's exports now has
    # to require it itself (approximately: `Require Import` does not
    # re-export, and tactics and hints are not in the `.glob`).
    before = {x: closure(deps, deps[x]) for x in files}
    changed = True
    while changed:
        changed = False
        for x in files:
            vis = closure(new, new[x])
            miss = sorted(m for m in refs[x]
                          if m not in vis and m in before[x])
            if miss:
                new[x] = new[x] + miss
                changed = True
                print(f'{x}: now also requires {", ".join(miss)}')
    fin, path, _ = critical(times, deps)
    nfin, npath, _ = critical(times, new)
    print(f'critical path {max(fin.values()):.0f} s -> '
          f'{max(nfin.values()):.0f} s, simulated -j{jobs} '
          f'{simulate(times, deps, order, jobs):.0f} s -> '
          f'{simulate(times, new, order, jobs):.0f} s')
    print('   time   finish  new critical path')
    for x in npath:
        if times.get(x, 0) >= 1 or x == npath[-1]:
            print(f'{times.get(x, 0):7.1f} {nfin[x]:8.1f}  {x}')


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('file', nargs='?')
    ap.add_argument('n', nargs='?', type=int, default=25)
    ap.add_argument('--ideal', action='store_true')
    ap.add_argument('--decls', action='store_true',
                    help='with FILE.v: also list every declaration')
    ap.add_argument('-j', type=int, default=4)
    ap.add_argument('--try', dest='edits', action='append', default=[],
                    metavar='FILE=A,B', help='replace FILE\'s Requires')
    args = ap.parse_args()
    times, deps, order = load([])
    if args.edits:
        n = int(args.file) if args.file else args.n
        report_try(args.edits, times, deps, order, args.j, n)
    elif args.file and args.file.endswith('.v'):
        report_file(args.file, times, deps, args.ideal, args.decls)
    elif args.ideal:
        n = int(args.file) if args.file else args.n
        report_ideal(times, deps, order, args.j, n)
    else:
        ap.print_help()


if __name__ == '__main__':
    signal.signal(signal.SIGPIPE, signal.SIG_DFL)
    main()
