"""Generate a syntactic push tactic from a family of push lemmas.

A push family is a list of lemmas `OP (C args) .. = ..` (e.g. `gren_tyPi :
(tyPi l l' A B)⟪ξ⟫ = tyPi l l' A⟪ξ⟫ B⟪ξ⟫`). Rewriting with every lemma in
turn (`repeat progress (rewrite ?l1, ..., ?ln)`) costs one traversal of the
goal per lemma per pass. The generated tactic instead finds an `OP t`
subterm syntactically and rewrites with the lemmas for `t`'s head only.

usage (inside the dev shell, after the lemmas' file is built):
  python3 tools/gen_push.py IMPORT OP ARGPOS NAME [--hyps] LEMMA...
    IMPORT  e.g. 'From DeLaM.Typing Require Import GWeakening.'
    OP      the pushed operation, e.g. gren, or several separated by commas
            (usubst_ty,usubst_tm); OP/N declares N implicit arguments for an
            operation not in IMPL below
    ARGPOS  index of the pushed term among OP's explicit arguments
    NAME    the tactic to define; NAME_at is its head table
    --hyps  also push in hypotheses (the old `rewrite ... in *`)
Prints the Ltac to paste in place of the old definition.
"""
import re, subprocess, sys, tempfile, os

def sexprs(s):
    """Tokenize a printed term into nested lists."""
    toks = re.findall(r'\(|\)|[^\s()]+', s)
    def parse(i):
        out = []
        while i < len(toks):
            t = toks[i]
            if t == '(':
                sub, i = parse(i + 1); out.append(sub)
            elif t == ')':
                return out, i + 1
            else:
                out.append(t); i += 1
        return out, i
    return parse(0)[0]

def head(x):
    while isinstance(x, list): x = x[0]
    return x.lstrip('@')

def main():
    args = sys.argv[1:]
    hyps = '--hyps' in args
    args = [a for a in args if a != '--hyps']
    imp, opspec, argpos, name = args[0], args[1], int(args[2]), args[3]
    lemmas = [w for a in args[4:] for w in a.split()]
    ops = []
    for o in opspec.split(','):
        o, _, n = o.partition('/')
        if n: IMPL[o] = int(n)
        assert o in IMPL, ('unknown implicit arity', o)
        ops.append(o)
    src = imp + "\nSet Printing Implicit.\nUnset Printing Notations.\nSet Printing Width 100000.\n"
    src += ''.join(f"Check {l}.\n" for l in lemmas)
    with tempfile.NamedTemporaryFile('w', suffix='.v', delete=False, dir='.') as f:
        f.write(src); tmp = f.name
    try:
        r = subprocess.run(['coqc', '-Q', 'theories', 'DeLaM', tmp],
                           capture_output=True, text=True)
        if r.returncode != 0:
            sys.exit('coqc failed:\n' + r.stdout[-2000:] + r.stderr[-2000:])
        out = r.stdout
    finally:
        base = tmp[:-2]
        aux = os.path.join(os.path.dirname(base), '.' + os.path.basename(base) + '.aux')
        for p in (base + '.v', base + '.vo', base + '.vok', base + '.vos', base + '.glob', aux):
            if os.path.exists(p): os.remove(p)
    blocks = [b for b in re.split(r'\n(?=\S)', out) if b.strip()]
    assert len(blocks) == len(lemmas), (len(blocks), len(lemmas))
    table, expl = {}, {}
    for l, b in zip(lemmas, blocks):
        assert b.startswith(l), (l, b[:80])
        typ = ' '.join(b.split(':', 1)[1].split())
        m = re.search(r'@eq \S+ ', typ)
        lhs = sexprs(typ[m.end():])[0]
        o = lhs[0].lstrip('@') if isinstance(lhs, list) else None
        assert o in ops, (l, 'LHS is not an application of', ops, lhs)
        n = len(lhs) - 1 - IMPL[o]
        assert expl.setdefault(o, n) == n, (l, 'arity', o, n)
        h = head(lhs[1 + IMPL[o] + argpos])
        table.setdefault(h, []).append(l)
        # a lemma stated on a sort's fixpoint (subst_ty) also serves the
        # class method goals are written with (T[d] is @subst ty _ T d)
        if h in ALIAS: table.setdefault(ALIAS[h], []).append(l)
    arms = []
    for h, ls in table.items():
        body = f"k {ls[0]}" if len(ls) == 1 else "first [" + " | ".join(f"k {x}" for x in ls) + "]"
        arms.append(f"  | @{h} => {body}")
    print(f"Ltac {name}_at h k := lazymatch h with")
    print('\n'.join(arms))
    print("  end.")
    print(f"Ltac {name} := repeat match goal with")
    for o in ops:
        holes = ' '.join('?t' if i == argpos else '_' for i in range(expl[o]))
        pat = f"@{o} {' '.join(['_'] * IMPL[o])} {holes}".replace('  ', ' ')
        print(f"  | |- context [{pat}] => let h := head_of t in {name}_at h ltac:(fun L => rewrite !L)")
        if hyps:
            print(f"  | H : context [{pat}] |- _ => let h := head_of t in {name}_at h ltac:(fun L => rewrite !L in H)")
    print("  end.")

# number of implicit arguments of each operation (the explicit ones are read
# off the lemmas)
IMPL = {'gren': 2, 'ren': 2, 'subst': 2, 'gsubst': 2, 'gwa': 2, 'usubst': 2}
# per-sort fixpoints and the class methods that unfold to them
ALIAS = {'ren_ty': 'ren', 'ren_tm': 'ren', 'subst_ty': 'subst', 'subst_tm': 'subst',
         'gren_ty': 'gren', 'gren_tm': 'gren', 'gcren': 'gren',
         'gsubst_ty': 'gsubst', 'gsubst_tm': 'gsubst',
         'usubst_ty': 'usubst', 'usubst_tm': 'usubst', 'ucsubst': 'usubst'}

if __name__ == '__main__':
    main()
