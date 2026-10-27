"""Shared helpers of the plan scripts: read a file at git HEAD, delete/insert top-level blocks."""
import os, re, subprocess, sys
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
import blocks as B

P = os.path.abspath(os.path.join(os.path.dirname(__file__), "../../.."))

def head(path):
    return subprocess.run(["git", "-C", P, "show", "HEAD:" + path], capture_output=True,
                          text=True, check=True).stdout

def txt(s): return "text \\<open>" + s.strip() + "\\<close>"

def scratch_blocks(path):
    """name -> text of the blocks of a scratch theory (primes stripped from the names)."""
    out = {}
    for b in B.split(open(os.path.join(P, path)).read()):
        if b["name"]:
            body = "\n".join(b["lines"]).rstrip("\n")
            out[b["name"].rstrip("'")] = body.replace(b["name"], b["name"].rstrip("'"), 1)
    return out

def edit(path, remove=(), remove_with_text=(), insert_after=(), replace=(), src=None):
    """remove: block names; remove_with_text: also the text block before them;
    insert_after: [(name, [blocks])]; replace: [(old, new)] on the final text."""
    text = src if src is not None else head(path)
    bl = B.split(text)
    drop, ins = set(), {}
    for n in list(remove) + list(remove_with_text):
        k = [i for i, b in enumerate(bl) if b["name"] == n]
        assert len(k) == 1, (path, n, k)
        drop.add(k[0])
        if n in remove_with_text:
            assert bl[k[0] - 1]["kind"] == "text", (path, n)
            drop.add(k[0] - 1)
    for n, new in insert_after:
        k = [i for i, b in enumerate(bl) if b["name"] == n]
        assert len(k) == 1, (path, n, k)
        ins[k[0]] = new
    out = []
    for i, b in enumerate(bl):
        if i not in drop:
            out += b["lines"]
        if i in ins:
            out += ("\n\n".join(ins[i]) + "\n").split("\n")
    s = "\n".join(out)
    s = re.sub(r"\n{3,}", "\n\n", s)
    for old, new in replace:
        assert s.count(old) == 1, (path, old[:60], s.count(old))
        s = s.replace(old, new)
    open(os.path.join(P, path), "w").write(s)
