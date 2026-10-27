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
    out, primed = {}, []
    for b in B.split(open(os.path.join(P, path)).read()):
        if b["name"]:
            out[b["name"].rstrip("'")] = "\n".join(b["lines"]).rstrip("\n")
            if b["name"].endswith("'"): primed.append(b["name"])
    for n in primed:                       # references to a primed name, anywhere
        out = {k: v.replace(n, n.rstrip("'")) for k, v in out.items()}
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

def strip_comments(text, drop):
    """Remove the inline comments `\\<comment> \\<open>...\\<close>` whose body satisfies drop(body)
    (nested cartouches respected); a comment that fills its lines takes the lines with it."""
    tok = "\\<comment> \\<open>"
    out, i = [], 0
    while True:
        j = text.find(tok, i)
        if j < 0:
            out.append(text[i:]); break
        k, depth = j + len(tok), 1
        while depth:
            o, c = text.find("\\<open>", k), text.find("\\<close>", k)
            assert c >= 0
            if 0 <= o < c: depth += 1; k = o + 7
            else: depth -= 1; k = c + 8
        body = text[j + len(tok):k - 8]
        if not drop(body):
            out.append(text[i:k]); i = k; continue
        ls = text.rfind("\n", 0, j) + 1
        le = text.find("\n", k); le = len(text) if le < 0 else le
        if text[ls:j].strip() == "" and text[k:le].strip() == "":
            out.append(text[i:ls]); i = le + 1
        else:
            out.append(text[i:j]); i = k
    return "".join(out)
