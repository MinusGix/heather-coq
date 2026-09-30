"""Generate a syntactic push tactic from a family of push lemmas.

A push family is a list of lemmas `OP (C args) .. = ..` (e.g. `gren_tyPi :
(tyPi l l' A B)⟪ξ⟫ = tyPi l l' A⟪ξ⟫ B⟪ξ⟫`). Rewriting with every lemma in
turn (`repeat progress (rewrite ?l1, ..., ?ln)`) costs one traversal of the
goal per lemma per pass. The generated tactic instead finds an `OP t`
subterm syntactically and rewrites with the lemmas for `t`'s head only.

usage (inside the dev shell, after the lemmas' file is built):
  python3 tools/gen_push.py IMPORT OP ARGPOS NAME [--hyps] LEMMA...
    IMPORT  e.g. 'From DeLaM.Typing Require Import GWeakening.'
    OP      the pushed operation, e.g. gren (a constant; implicit arguments
            are skipped)
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
    imp, op, argpos, name = args[0], args[1], int(args[2]), args[3]
    lemmas = [w for a in args[4:] for w in a.split()]
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
    blocks = re.split(r'\n(?=\S)', out)
    table = {}
    for l, b in zip(lemmas, [b for b in blocks if b.strip()]):
        assert b.startswith(l), (l, b[:80])
        typ = ' '.join(b.split(':', 1)[1].split())
        m = re.search(r'@eq \S+ ', typ)
        lhs = sexprs(typ[m.end():])[0]
        assert isinstance(lhs, list) and lhs[0].lstrip('@') == op, (l, lhs)
        assert len(lhs) == 1 + IMPL[op] + EXPL[op], (l, 'arity', lhs)
        table.setdefault(head(lhs[1 + IMPL[op] + argpos]), []).append(l)
    arms = []
    for h, ls in table.items():
        body = f"k {ls[0]}" if len(ls) == 1 else "first [" + " | ".join(f"k {x}" for x in ls) + "]"
        arms.append(f"  | @{h} => {body}")
    holes = ' '.join('?t' if i == argpos else '_' for i in range(EXPL[op]))
    pat = f"@{op} {' '.join(['_'] * IMPL[op])} {holes}"
    print(f"Ltac {name}_at h k := lazymatch h with")
    print('\n'.join(arms))
    print("  end.")
    print(f"Ltac {name} := repeat match goal with")
    print(f"  | |- context [{pat}] => let h := head_of t in {name}_at h ltac:(fun L => rewrite L)")
    if hyps:
        print(f"  | H : context [{pat}] |- _ => let h := head_of t in {name}_at h ltac:(fun L => rewrite L in H)")
    print("  end.")

# arity of each operation: implicit and explicit arguments
IMPL = {'gren': 2, 'ren': 2, 'subst': 2, 'gsubst': 2, 'gwa': 2, 'usubst': 2}
EXPL = {'gren': 2, 'ren': 2, 'subst': 2, 'gsubst': 2, 'gwa': 2, 'usubst': 2}

if __name__ == '__main__':
    main()
