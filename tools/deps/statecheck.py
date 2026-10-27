"""statecheck.py OLD.tsv NEW.tsv: compare the constants and types in every fact's statement
between two scans (scan.sh), by fact base name.  A difference means a statement now reads
differently, e.g. a free variable captured by a constant that became visible.  CHECK_SESSIONS
(comma-separated) selects the theories; RENAMES (old=new,...) maps renamed facts."""
import collections, os, sys
old_f, new_f = sys.argv[1], sys.argv[2]
SESS = tuple(x + "." for x in os.environ.get("CHECK_SESSIONS",
             "Quantum_Computing_by_VP,Essential_Functional_Analysis").split(","))
LIB = ("Quantum_Computing_by_VP.", "Essential_Functional_Analysis.", "HHL_Algorithm")
REN = dict(x.split("=") for x in os.environ.get("RENAMES", "").split(",") if x)
def load(f, ren):
    st = collections.defaultdict(collections.Counter)
    for l in open(f):
        thy, fact, kind, owner, name = l.rstrip("\n").split("\t")
        if not thy.startswith(SESS): continue
        base = fact.split(".", 1)[1]
        base = ren.get(base, base)
        if kind in ("const", "type"):
            # owners may have moved: project entities are compared by base name
            st[base][(kind, name.split(".")[-1] if owner.startswith(LIB) else name)] += 1
        else:
            st[base]
    return st
old, new = load(old_f, REN), load(new_f, {})
missing, added = sorted(set(old) - set(new)), sorted(set(new) - set(old))
diff = [(k, sorted(set(new[k]) - set(old[k])), sorted(set(old[k]) - set(new[k])))
        for k in sorted(set(old) & set(new)) if set(old[k]) != set(new[k])]
print(f"facts: old {len(old)}, new {len(new)}; missing {len(missing)}, added {len(added)}, "
      f"changed statements {len(diff)}")
for k in missing[:40]: print("  MISSING", k)
for k in added[:40]: print("  ADDED", k)
for k, a, r in diff[:60]: print(f"  CHANGED {k}: +{a} -{r}")
