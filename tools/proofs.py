#!/usr/bin/env python3
"""Where the time goes inside files: the slowest proofs and sentences.

Reads the per-sentence `.v.timing` files a `make TIMING=1` build writes
(or `tools/build-profile`), groups each file's sentences into
declarations (a `Lemma`/`Definition`/... statement up to its `Qed`,
`Defined` or the next declaration), and prints the slowest ones with
`file:line`, split into the time of their tactics and of their `Qed`
(the kernel re-check). A `Qed` much slower than its tactics is the
symptom of a raw fixpoint or a big term left in the proof (docs/gotchas.md,
build-time gotchas).

Usage (from the repository root):
  tools/proofs.py [-n N] [FILE.v ...]     N slowest proofs (default 30),
                                          over the given files or all
  tools/proofs.py --sentences [-n N] ...  N slowest single sentences
  tools/proofs.py --save SNAP.tsv         write every declaration's time
  tools/proofs.py --diff A.tsv B.tsv [-n N]
                                          per-declaration deltas, largest
                                          first, and the per-file totals

A snapshot is keyed by file and declaration name, so it survives edits
that move lines; compare snapshots taken on one machine only.
"""
import argparse
import glob
import os
import re
import signal
import sys

LINE = re.compile(r'^Chars (\d+) - (\d+) \[(.*)\] ([\d.]+) secs')
DECL = re.compile(
    r'^\s*(?:#\[[^\]]*\]\s*)*(?:(?:Local|Global|Polymorphic|Monomorphic|'
    r'Program|Equations\?|Let)\s+)*'
    r'(Lemma|Theorem|Corollary|Fact|Remark|Proposition|Definition|Fixpoint|'
    r'CoFixpoint|Instance|Example|Equations|Inductive|CoInductive|Record|'
    r'Class|Scheme|Combined Scheme|Obligation|Next Obligation|Ltac|Ltac2|'
    r'Notation|Hint|Derive)\b\s*([^\s:({\[]*)')
END = re.compile(r'^\s*(Qed|Defined|Admitted|Save|Abort)\b')
PROOF_KINDS = {'Lemma', 'Theorem', 'Corollary', 'Fact', 'Remark',
               'Proposition', 'Definition', 'Fixpoint', 'CoFixpoint',
               'Instance', 'Example', 'Equations', 'Obligation',
               'Next Obligation'}


def sentences(timing):
    src = timing[:-len('.timing')]
    try:
        data = open(src, 'rb').read()
    except OSError:
        data = None
    out = []
    for raw in open(timing, encoding='utf-8', errors='replace'):
        m = LINE.match(raw)
        if not m:
            continue
        a, b, t = int(m.group(1)), int(m.group(2)), float(m.group(4))
        if data is not None:
            text = data[a:b].decode('utf-8', errors='replace')
            line = data.count(b'\n', 0, a) + 1
            # The span starts at the sentence, possibly after blank lines
            # and comments that coqc skipped.
            stripped = re.sub(r'\(\*.*?\*\)', ' ', text, flags=re.S).lstrip()
            line += text[:len(text) - len(text.lstrip())].count('\n')
        else:
            stripped, line = m.group(3).replace('~', ' '), 0
        out.append((line, stripped, t))
    return src, out


def declarations(timing):
    """[(file, line, kind, name, tactic s, qed s)] for one file."""
    src, sents = sentences(timing)
    decls = []
    cur = None
    for line, text, t in sents:
        m = DECL.match(text)
        if m:
            kind = re.sub(r'\s+', ' ', m.group(1))
            name = m.group(2) or '_'
            cur = [src, line, kind, name, t, 0.0]
            decls.append(cur)
            continue
        if cur is None:
            # A command outside any proof (Require, Print Assumptions, …):
            # its own entry, named by its first words.
            words = text.split()
            kind = words[0] if words else '?'
            name = ' '.join(words[1:3])[:40]
            decls.append((src, line, kind, name, t, 0.0))
            continue
        if END.match(text):
            cur[5] += t
            cur = None if cur[2] in PROOF_KINDS else cur
        else:
            cur[4] += t
    return [tuple(d) for d in decls]


def timings(files):
    if files:
        out = []
        for f in files:
            f = f if f.endswith('.timing') else f + '.timing'
            if not f.endswith('.v.timing'):
                f = f[:-len('.timing')] + '.v.timing'
            out.append(f)
        return out
    return sorted(glob.glob('theories/**/*.v.timing', recursive=True))


def fmt_decl(d):
    src, line, kind, name, tac, qed = d
    tot = tac + qed
    flag = '  <- Qed-heavy' if qed > 1.0 and qed > tac else ''
    return (f'{tot:8.2f}  {tac:8.2f}  {qed:7.2f}  {src}:{line}  '
            f'{kind} {name}{flag}')


def load_snapshot(path):
    snap = {}
    for raw in open(path):
        if raw.startswith('#'):
            continue
        f, kind, name, tac, qed = raw.rstrip('\n').split('\t')
        key = (f, kind, name)
        # Duplicate names in one file (section copies) accumulate.
        old = snap.get(key, (0.0, 0.0))
        snap[key] = (old[0] + float(tac), old[1] + float(qed))
    return snap


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('files', nargs='*')
    ap.add_argument('-n', type=int, default=30)
    ap.add_argument('--sentences', action='store_true')
    ap.add_argument('--save')
    ap.add_argument('--diff', nargs=2, metavar=('A', 'B'))
    args = ap.parse_args()

    if args.diff:
        a, b = map(load_snapshot, args.diff)
        rows = []
        for k in set(a) | set(b):
            ta, tb = sum(a.get(k, (0, 0))), sum(b.get(k, (0, 0)))
            rows.append((tb - ta, ta, tb, k))
        rows.sort(key=lambda r: -abs(r[0]))
        print(f"total {sum(r[1] for r in rows):.0f} s -> "
              f"{sum(r[2] for r in rows):.0f} s")
        print('   delta    before     after  declaration')
        for d, ta, tb, (f, kind, name) in rows[:args.n]:
            print(f'{d:+8.2f}  {ta:8.2f}  {tb:8.2f}  {f}  {kind} {name}')
        files = {}
        for d, ta, tb, (f, _, _) in rows:
            x = files.setdefault(f, [0.0, 0.0])
            x[0] += ta
            x[1] += tb
        print('per file (largest change first):')
        for f, (ta, tb) in sorted(files.items(),
                                  key=lambda i: -abs(i[1][1] - i[1][0]))[:args.n]:
            print(f'{tb - ta:+8.2f}  {ta:8.2f}  {tb:8.2f}  {f}')
        return

    tfiles = timings(args.files)
    if not tfiles:
        sys.exit('no .v.timing files: run `make TIMING=1` '
                 '(or tools/build-profile) first')

    if args.sentences:
        rows = []
        for t in tfiles:
            src, sents = sentences(t)
            rows += [(s, src, line, text) for line, text, s in sents]
        rows.sort(reverse=True)
        for s, src, line, text in rows[:args.n]:
            text = re.sub(r'\s+', ' ', text)[:70]
            print(f'{s:8.2f}  {src}:{line}  {text}')
        return

    decls = [d for t in tfiles for d in declarations(t)]
    if args.save:
        with open(args.save, 'w') as fh:
            fh.write('#file\tkind\tname\ttactics\tqed\n')
            for src, line, kind, name, tac, qed in decls:
                fh.write(f'{src}\t{kind}\t{name}\t{tac:.3f}\t{qed:.3f}\n')
        print(f'wrote {len(decls)} declarations to {args.save}')
        return
    total = sum(d[4] + d[5] for d in decls)
    qed = sum(d[5] for d in decls)
    print(f'{len(tfiles)} files, {len(decls)} declarations, {total:.0f} s '
          f'of sentences ({qed:.0f} s in Qed/Defined)')
    print('   total   tactics      qed  declaration')
    for d in sorted(decls, key=lambda d: -(d[4] + d[5]))[:args.n]:
        print(fmt_decl(d))


if __name__ == '__main__':
    signal.signal(signal.SIGPIPE, signal.SIG_DFL)
    main()
