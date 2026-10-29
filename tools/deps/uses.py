"""uses.py SCAN.tsv THEORY [PREFIX...]: for each fact of THEORY (base name), the project
theories whose facts its proof uses and whose constants/types its statement mentions,
with the entities from outside THEORY; PREFIX limits the owners shown (default: the
project sessions)."""
import sys, collections
scan, thy = sys.argv[1], sys.argv[2]
prefixes = tuple(sys.argv[3:]) or ("Quantum_Computing_CP_Maps.", "Matrix_Analysis_Prerequisites.")
facts = collections.OrderedDict()
for l in open(scan):
    t, fact, kind, owner, name = l.rstrip("\n").split("\t")
    if t.split(".")[-1] != thy: continue
    f = facts.setdefault(fact.split(".", 1)[1], collections.defaultdict(set))
    if owner.startswith(prefixes) and owner.split(".")[-1] != thy:
        f[owner.split(".")[-1]].add(("" if kind == "dep" else kind + " ") + name.split(".")[-1])
for fact, own in facts.items():
    print(fact + ": " + "; ".join(f"{o} [{', '.join(sorted(v))}]" for o, v in sorted(own.items())))
