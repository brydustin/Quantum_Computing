"""Trusted share of a headline theorem, after Lean-QuantumAlg's measure: lines of our own
definitions that the statement depends on (closure from trust.ML), plus the statement itself,
over the lines of our theories in the theorem's import closure.
trust.py TRUST.tsv ANC.tsv EXPORT_DIR"""
import sys, os, re, glob, collections
sys.path.insert(0, os.path.dirname(__file__))
from blocks import split

trust, anc, root = sys.argv[1:4]
OURS = ("Hermitian_Functional_Calculus.", "Matrix_Analysis_Prerequisites.",
        "Quantum_Computing_CP_Maps.", "HHL_Algorithm.")
files = {os.path.basename(f)[:-4]: f for f in glob.glob(root + "/**/*.thy", recursive=True)}
def nonblank(ls): return sum(1 for l in ls if l.strip())
blocks_cache = {}
def blocks(f):
    if f not in blocks_cache:
        blocks_cache[f] = split(open(f).read())
    return blocks_cache[f]
def block_at(f, line):
    for b in blocks(f):
        if b["line"] <= line < b["line"] + len(b["lines"]): return b
    return None

closure = collections.defaultdict(set)
for l in open(anc):
    tgt, thy = l.rstrip("\n").split("\t")
    if thy.startswith(OURS): closure[tgt].add(thy.split(".", 1)[1])
items = collections.defaultdict(list)
for l in open(trust):
    t, kind, name, owner, f, line, own = l.rstrip("\n").split("\t"); f = os.path.expanduser(f)
    if own == "1": items[t].append((name, f, int(line)))

STMT = {"hhl_rus_total": ("HHL_Termination", ["hhl_rus_total", "hhl_rus_expected_rounds"]),
        "hhl_lap_sparse": ("HHL_Laplacian_Sparse", ["hhl_lap_sparse"])}
for key, (thy, facts) in STMT.items():
    tgts = [t for t in items if t.split(":")[1] in facts]
    defs = {}
    for t in tgts:
        for name, f, line in items[t]:
            b = block_at(f, line) if f else None
            if b: defs[(f, b["line"])] = (name, nonblank(b["lines"]))
    def_lines = sum(n for _, n in defs.values())
    # statement: the enclosing context header (fixes/assumes) and the theorem up to its proof
    f = files[thy]; text = open(f).read().split("\n"); stmt = 0
    for fact in facts:
        i = next(i for i, l in enumerate(text) if re.match(r"(theorem|corollary|lemma) %s\b" % fact, l))
        j = i
        while not re.match(r"\s*(proof|by|using|apply|unfolding)\b", text[j + 1]): j += 1
        stmt += nonblank(text[i:j + 1])
    ctx = [b for b in blocks(f) if b["kind"] == "context"]
    first = next(i for i, l in enumerate(text) if re.match(r"(theorem|corollary|lemma) %s\b" % facts[0], l)) + 1
    ctx = [b for b in ctx if b["line"] < first and any(l.strip() == "begin" for l in b["lines"])][-1:]
    hdr = 0
    for b in ctx:
        k = next(i for i, l in enumerate(b["lines"]) if l.strip() == "begin")
        hdr += nonblank(b["lines"][:k + 1])
    total = sum(nonblank(open(files[th.split(".")[-1]]).read().split("\n")) for th in closure[tgts[0].split(":")[0]])
    whole = sum(nonblank(open(x).read().split("\n")) for x in files.values())
    trusted = def_lines + stmt + hdr
    print(f"{key}: {len(defs)} definitions, {def_lines} lines; statement {stmt + hdr} lines; "
          f"trusted {trusted}; closure {len(closure[tgts[0].split(':')[0]])} theories, {total} lines "
          f"-> {100*trusted/total:.2f}%; whole development {whole} lines -> {100*trusted/whole:.2f}%")
    for (ff, _), (name, n) in sorted(defs.items(), key=lambda x: -x[1][1])[:8]:
        print(f"   {n:4d}  {name}  ({os.path.basename(ff)})")
