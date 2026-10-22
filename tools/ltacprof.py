#!/usr/bin/env python3
"""Profile one proof: its sentences' times and Coq's Ltac profile.

Copies FILE.v into a scratch directory, cut after the end of the
declaration at LINE (or named NAME), with `Set Ltac Profiling.` before
the declaration and `Show Ltac Profile CutOff C.` after its `Qed`, then
compiles it with `coqc -time` against the built tree (`-Q theories
DeLaM`; the file's dependencies must be built, e.g. by `make` or
`make vos`, since the cut copy is checked in full only up to LINE).

Usage (from the repository root, inside the dev shell):
  tools/ltacprof.py theories/X/File.v LINE|NAME [--cutoff C] [-n N]
  tools/ltacprof.py theories/X/File.v --file [--cutoff C]

  --cutoff C  hide tactics under C percent of the total (default 1)
  -n N        sentences to show, slowest first (default 15)
  --file      profile the whole file (`coqc -profile-ltac`) instead
  --keep      leave the scratch copy and print its path

The profile's "total" column counts a tactic's time including the
tactics it calls; "local" excludes them. A big `eauto`/`first` self time
with few successes is a search that mostly fails (docs/gotchas.md,
build-time gotchas). The profiler adds overhead, so its seconds read
high; the sentence times printed next to it come from the same run.
"""
import argparse
import os
import re
import signal
import shutil
import subprocess
import sys
import tempfile

DECL = re.compile(
    r'^[ \t]*(?:#\[[^\]]*\][ \t]*)*(?:(?:Local|Global|Program|Polymorphic)[ \t]+)*'
    r'(?:Lemma|Theorem|Corollary|Fact|Remark|Proposition|Definition|Fixpoint|'
    r'CoFixpoint|Instance|Example|Equations)[ \t]+([^\s:({\[]+)', re.M)
END = re.compile(r'\b(?:Qed|Defined|Admitted|Save[ \t]+\S+|Abort)\s*\.', re.M)


def find_decl(src, target):
    decls = [(src.count('\n', 0, m.start()) + 1, m.start(), m.group(1))
             for m in DECL.finditer(src)]
    if target.isdigit():
        line = int(target)
        best = [d for d in decls if d[0] <= line]
        if not best:
            sys.exit(f'no declaration at or before line {line}')
        return best[-1]
    hits = [d for d in decls if d[2] == target]
    if not hits:
        sys.exit(f'no declaration named {target}')
    if len(hits) > 1:
        print(f'note: {len(hits)} declarations named {target}; '
              f'profiling the first (line {hits[0][0]}); pass a line '
              'number to pick another', file=sys.stderr)
    return hits[0]


def coqc(args, cwd):
    return subprocess.run(['coqc', '-Q', os.path.join(cwd, 'theories'),
                           'DeLaM', '-w', '-notation-overridden'] + args,
                          capture_output=True, text=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('file')
    ap.add_argument('target', nargs='?')
    ap.add_argument('--cutoff', type=int, default=1)
    ap.add_argument('-n', type=int, default=15)
    ap.add_argument('--file', dest='whole', action='store_true')
    ap.add_argument('--keep', action='store_true')
    args = ap.parse_args()
    root = os.getcwd()
    if not shutil.which('coqc'):
        sys.exit('coqc not found: run inside `nix develop path:.`')
    if args.whole:
        r = coqc(['-profile-ltac', '-profile-ltac-cutoff', str(args.cutoff),
                  '-o', os.devnull, args.file], root)
        sys.stdout.write(r.stdout)
        sys.stderr.write(r.stderr)
        sys.exit(r.returncode)
    if not args.target:
        ap.error('give a LINE or NAME (or --file)')

    src = open(args.file, encoding='utf-8').read()
    line, start, name = find_decl(src, args.target)
    end = END.search(src, start)
    if not end:
        sys.exit(f'{name}: no Qed/Defined after line {line}')
    cut = (src[:start] + 'Set Ltac Profiling.\n' + src[start:end.end()]
           + f'\nShow Ltac Profile CutOff {args.cutoff}.\n')
    tmp = tempfile.mkdtemp(prefix='ltacprof-')
    # Same base name, so `Module`s and error messages read the same.
    scratch = os.path.join(tmp, os.path.basename(args.file))
    open(scratch, 'w', encoding='utf-8').write(cut)
    timing = scratch + '.timing'
    print(f'profiling {name} ({args.file}:{line}) ...', file=sys.stderr)
    r = coqc(['-time-file', timing, '-o', os.path.splitext(scratch)[0] + '.vo',
              scratch], root)
    out = r.stdout
    # The cut copy may leave a section or module open; that error comes
    # after the profile and is expected.
    bad = r.returncode != 0 and 'total time:' not in out
    if bad:
        sys.stderr.write(r.stdout + r.stderr)
        sys.exit(f'coqc failed before reaching {name} (scratch: {scratch})')

    data = cut.encode('utf-8')
    rows = []
    for raw in open(timing, encoding='utf-8', errors='replace'):
        m = re.match(r'^Chars (\d+) - (\d+) \[.*\] ([\d.]+) secs', raw)
        if m and int(m.group(1)) >= len(src[:start].encode('utf-8')):
            a, b = int(m.group(1)), int(m.group(2))
            text = re.sub(r'\s+', ' ', data[a:b].decode('utf-8', 'replace'))
            ln = data.count(b'\n', 0, a)  # the inserted line shifts by one
            rows.append((float(m.group(3)), ln, text))
    tot = sum(r[0] for r in rows)
    print(f'{name} ({args.file}:{line}): {tot:.2f} s over {len(rows)} '
          f'sentences (under the profiler)')
    for t, ln, text in sorted(rows, reverse=True)[:args.n]:
        print(f'  {t:7.2f}  {args.file}:{ln}  {text[:80]}')
    # coqc prints the profile again at exit while profiling is on.
    i = out.find('total time:')
    j = out.find('total time:', i + 1) if i >= 0 else -1
    print()
    print(out[i:j] if j >= 0 else out[i:] if i >= 0 else out)
    if args.keep:
        print(f'scratch copy: {scratch}', file=sys.stderr)
    else:
        shutil.rmtree(tmp)


if __name__ == '__main__':
    signal.signal(signal.SIGPIPE, signal.SIG_DFL)
    main()
