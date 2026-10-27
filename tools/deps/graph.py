"""Block-level dependencies of theories from a scan (scan.sh) and the sources.
deps(scan, files) -> {(theory, block index): set of (theory, block index)} for the blocks
of the given theory files, by the facts the proofs use and the constants and types the
statements mention.  As a script: graph.py SCAN FILE... prints each block's dependencies."""
import collections, os, re, sys
sys.path.insert(0, os.path.dirname(__file__))
import blocks as B

def load(files):
    out = {}
    for f in files:
        thy = os.path.basename(f)[:-4]
        out[thy] = B.split(open(f).read())
    return out

def owners(blks):
    """entity base name -> block index, for facts (name, name_def, ...) and constants."""
    own = {}
    for i, b in enumerate(blks):
        if b["name"]:
            own[b["name"]] = i
    return own

def deps(scan, files):
    blks = load(files)
    own = {t: owners(bl) for t, bl in blks.items()}
    def find(thy, ent):
        o = own.get(thy, {})
        for cand in (ent, re.sub(r"(_def|\.simps|_raw_def|\.\w+|_\d+)$", "", ent)):
            if cand in o: return o[cand]
        return None
    g = collections.defaultdict(set)
    for l in open(scan):
        t, fact, kind, owner, name = l.rstrip("\n").split("\t")
        t, owner = t.split(".")[-1], owner.split(".")[-1]
        if t not in blks or owner not in blks: continue
        src = find(t, fact.split(".", 1)[1])
        dst = find(owner, name.split(".", 1)[1] if "." in name else name)
        if src is not None and dst is not None and (t, src) != (owner, dst):
            g[(t, src)].add((owner, dst))
    return blks, g

if __name__ == "__main__":
    blks, g = deps(sys.argv[1], sys.argv[2:])
    for (t, i), ds in sorted(g.items()):
        print(f"{t}:{i} {blks[t][i]['name']} <- " + ", ".join(
            f"{'' if dt == t else dt + ':'}{blks[dt][di]['name']}" for dt, di in sorted(ds)))
