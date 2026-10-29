"""imports.py SCAN [MOVES.json]: minimal project imports of the notes theories, from the facts,
constants and types they use (a scan, see scan.sh), after relocating the entities listed in
MOVES ({base name: new theory}).  Prints the theories whose project imports would change.
Blind spots: notation, abbreviations, text antiquotations (check with grep)."""
import collections, json, os, re, sys
P = os.path.join(os.path.dirname(__file__), "../..")
SESS = ("Quantum_Computing_CP_Maps", "Matrix_Analysis_Prerequisites")
moves = json.load(open(sys.argv[2])) if len(sys.argv) > 2 else {}
root = open(os.path.join(P, "ROOT")).read()
order = re.findall(r"^\s+(Day\d\d_\w+|Quantum_Channels|QC_Notes_Overview)\s*$", root, re.M)
bundle = ["Matrix_Lemmas", "Unitary_Tensor_Algebra", "Matrix_Typed", "Lmat_Euclidean"]
def cur_imports(t):
    d = "Matrix_Analysis_Prerequisites" if t in bundle else "."
    s = open(os.path.join(P, d, t + ".thy")).read()
    m = re.search(r"imports(.*?)\bbegin\b", s, re.S)
    return [x.strip('"').split(".")[-1] for x in m.group(1).split()]
need = collections.defaultdict(set)
for l in open(sys.argv[1]):
    t, fact, kind, owner, name = l.rstrip("\n").split("\t")
    if not owner.startswith(SESS): continue
    t, owner = t.split(".")[-1], owner.split(".")[-1]
    base = name.split(".")[-1]
    owner = moves.get(base, moves.get(re.sub(r"_def$", "", base), owner))
    if moves.get(fact.split(".", 1)[1]):
        t = moves[fact.split(".", 1)[1]]
    if owner != t: need[t].add(owner)
anc = {}
def ancestors(t, imps):
    if t not in anc:
        a = set()
        for i in imps.get(t, []):
            a |= {i} | ancestors(i, imps)
        anc[t] = a
    return anc[t]
imps = {t: [i for i in cur_imports(t) if i in bundle] for t in bundle}
for t in order:
    if t == "QC_Notes_Overview": continue
    n = {x for x in need[t] if x in order or x in bundle}
    for x in list(n):
        ancestors(x, imps)
    minimal = sorted(n - set().union(*[anc[x] for x in n]) if n else set(),
                     key=lambda x: (x not in bundle, order.index(x) if x in order else 0))
    old = [i for i in cur_imports(t) if i in order or i in bundle]
    imps[t] = minimal
    if set(minimal) != set(old):
        print(f"{t}: {' '.join(old)}  ->  {' '.join(minimal)}")
