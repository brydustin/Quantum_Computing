"""audit.py SCAN... : where the notes theories are long or cluttered.  Per theory: lines, proof
blocks, the longest proofs, bookkeeping lemmas (carrier/dims/index/entry), nested `foldr`
definitions, process comments, and facts no proof in any scan uses (dead unless a text cites them).
Pass every scan whose facts may use the notes (notes, HHL, Demo)."""
import collections, os, re, sys
sys.path.insert(0, os.path.dirname(__file__))
import blocks as B
P = os.path.join(os.path.dirname(__file__), "../..")
HEAD = ("theorem", "corollary", "proposition")
BOOK = re.compile(r"(_carrier|_dims?$|_dim_(row|col)|_index|_idx|_nth$|_length$|_entry|_len$|_Nil$|_Cons$|_simps?$)")
PROCESS = re.compile(r"\\<comment>\s*\\<open>\s*(Step|Now|Apply|We |Build|Define|Lift|Pointwise|Per-entry|Adjoint|From|Then|This |Here)")
used = set()
own = {}
for scan in sys.argv[1:]:
    for l in open(scan):
        thy, fact, kind, owner, name = l.rstrip("\n").split("\t")
        if kind == "dep": used.add(name.split(".")[-1] if owner.startswith(("Quantum_Computing_by_VP", "Essential_Functional_Analysis")) else name)
        if kind == "const" and owner.startswith(("Quantum_Computing_by_VP", "Essential_Functional_Analysis")):
            used.add(name.split(".")[-1])          # a constant used in a statement keeps its definition
        own[fact.split(".", 1)[1]] = thy.split(".")[-1]
root = open(os.path.join(P, "ROOT")).read()
thys = [("Essential_Functional_Analysis/" + t, t) for t in ["Matrix_Lemmas", "Unitary_Tensor_Algebra", "Matrix_Typed", "Lmat_Euclidean"]]
thys += [(t, t) for t in re.findall(r"^\s+(Day\d\d_\w+|Quantum_Channels)\s*$", root, re.M)]
texts = "".join(open(os.path.join(P, f + ".thy")).read() for f, _ in thys)
texts += open(os.path.join(P, "QC_Notes_Overview.thy")).read() + open(os.path.join(P, "NOTES_AUDIT.md")).read()
import glob
for f in glob.glob(os.path.join(P, "Algorithms", "**", "*.thy"), recursive=True) + \
         glob.glob(os.path.join(P, "tools", "check", "**", "*.thy"), recursive=True) + [os.path.join(P, "paper", "paper.tex")]:
    texts += open(f).read()      # a name in a `using` the proof did not need is invisible to the scan
cited = set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", texts))   # crude: a name that appears anywhere outside its block
rows, dead_all = [], []
for f, t in thys:
    src = open(os.path.join(P, f + ".thy")).read()
    bl = B.split(src)
    proofs = [b for b in bl if b["kind"] in ("lemma", "theorem", "corollary", "proposition")]
    longest = sorted(proofs, key=lambda b: -len(b["lines"]))[:3]
    book = [b for b in proofs if BOOK.search(b["name"] or "")]
    folds = len(re.findall(r"^\s*\"?\w+.*\\<equiv>\s*$|foldr \(\\<lambda>", src, re.M))
    folds = src.count("foldr (\\<lambda>")
    process = len(PROCESS.findall(src))
    dead = []
    for b in proofs:
        n = b["name"]
        if b["kind"] in HEAD or n in used: continue
        # cited in a text/antiquotation elsewhere? count occurrences outside this block
        if texts.count(n) - "\n".join(b["lines"]).count(n) > 0: continue
        dead.append((n, len(b["lines"])))
    for b in bl:
        if b["kind"] == "definition" and b["name"] and b["name"] not in used and b["name"] + "_def" not in used \
           and texts.count(b["name"]) - "\n".join(b["lines"]).count(b["name"]) == 0:
            dead.append((b["name"] + " (def)", len(b["lines"])))
    dead_all += [(t, n, k) for n, k in dead]
    rows.append((t, len(src.split("\n")), len(proofs), sum(len(b["lines"]) for b in book), folds, process,
                 sum(k for _, k in dead), ", ".join(f"{b['name']} {len(b['lines'])}" for b in longest)))
print(f"{'theory':30s} {'lines':>5s} {'prf':>4s} {'book':>5s} {'fold':>4s} {'proc':>4s} {'dead':>5s}  longest")
for r in sorted(rows, key=lambda r: -r[1]):
    print(f"{r[0]:30s} {r[1]:5d} {r[2]:4d} {r[3]:5d} {r[4]:4d} {r[5]:4d} {r[6]:5d}  {r[7]}")
print("\nunused facts (no proof in the scans uses them, no text cites them):")
for t, n, k in dead_all:
    print(f"  {t:30s} {n} ({k})")
