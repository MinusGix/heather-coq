"""Insert `Proof using ...` (Coq's first suggestion) into a .v file's lemmas.

`make vos` skips a section lemma's proof only when it says which section
variables it uses. To annotate a file: compile a copy with
`Set Suggest Proof Using.` after its imports, save coqc's output, then
    python3 tools/add_proof_using.py theories/X/File.v output.txt
Suggestions arrive in file order; a cursor walks the file so that a name
declared in two sections gets each its own clause."""
import re,sys
path,out=sys.argv[1],sys.argv[2]
s=open(path,encoding='utf-8').read()
lines=open(out,encoding='utf-8').read().replace('\nshould start',' should start').split('\n')
sug=[]
for i,l in enumerate(lines):
    m=re.match(r"The proof of (\S+) should start with one of the following commands:(.*)",l)
    if m:
        # a long name wraps the message, which can put the first
        # suggestion on the same line
        u=(m.group(2) or lines[i+1]).strip()
        assert u.startswith('Proof using') and u.endswith('.'),u
        sug.append((m.group(1),u))
kw=r"(?:Lemma|Theorem|Corollary|Fact|Remark|Proposition|Definition|Instance|Fixpoint|Example)"
pos=0;done=0
for name,u in sug:
    m=re.compile(r"(?m)^[ \t]*(?:#\[[^\]]*\][ \t]*)?(?:Local |Global )?"+kw+r"\s+"+re.escape(name)+r"(?![\w'])").search(s,pos)
    assert m,("declaration not found after cursor",name)
    p=re.compile(r"\bProof\.").search(s,m.end())
    q=re.compile(r"\b(?:Qed|Defined|Admitted)\.").search(s,m.end())
    assert p and (not q or p.start()<q.start()),("no Proof. before end",name)
    s=s[:p.start()]+u+s[p.end():]; done+=1
    pos=p.start()+len(u)
open(path,'w',encoding='utf-8').write(s)
print(f"{path}: {done}/{len(sug)} annotated")
