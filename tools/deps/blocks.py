"""Split a theory into top-level commands.  A command starts at a line that begins (column 0)
with an outer keyword, outside strings, comments and cartouches.  As a script:
blocks.py FILE prints index, first line, kind, name and size of every block."""
import re, sys

KEYWORDS = ("lemma theorem corollary proposition definition fun primrec function abbreviation "
            "inductive text txt section subsection subsubsection paragraph chapter declare lemmas "
            "notation no_notation hide_const hide_fact hide_type type_synonym datatype record "
            "context locale interpretation ML ML_val setup end theory named_theorems bundle "
            "unbundle instantiation instance consts axiomatization").split()
START = re.compile(r"^(%s)\b" % "|".join(KEYWORDS))

def depth_changes(line, state):
    """Advance the lexer state (cartouche depth, in_string, comment depth) over one line."""
    cart, instr, com = state
    i = 0
    while i < len(line):
        if instr:
            if line.startswith("\\\"", i): i += 2; continue
            if line[i] == '"': instr = False
            i += 1; continue
        if line.startswith("(*", i): com += 1; i += 2; continue
        if com and line.startswith("*)", i): com -= 1; i += 2; continue
        if com: i += 1; continue
        if line.startswith("\\<open>", i): cart += 1; i += 7; continue
        if line.startswith("\\<close>", i): cart -= 1; i += 8; continue
        if line[i] == '"' and not cart: instr = True
        i += 1
    return cart, instr, com

def split(text):
    lines = text.split("\n")
    blocks, cur, state = [], [], (0, False, 0)
    for l in lines:
        if state == (0, False, 0) and START.match(l) and cur:
            blocks.append(cur); cur = []
        cur.append(l)
        state = depth_changes(l, state)
    blocks.append(cur)
    out, ln = [], 1
    for b in blocks:
        m = START.match(b[0])
        kind = m.group(1) if m else "pre"
        nm = re.match(r"^\w+\s+([A-Za-z_][A-Za-z0-9_']*)", b[0])
        name = nm.group(1) if nm and kind in ("lemma", "theorem", "corollary", "proposition",
                                               "definition", "fun", "abbreviation", "lemmas") else ""
        out.append({"line": ln, "kind": kind, "name": name, "lines": b})
        ln += len(b)
    return out

if __name__ == "__main__":
    for i, b in enumerate(split(open(sys.argv[1]).read())):
        print(f"{i:4d} {b['line']:5d} {len(b['lines']):5d} {b['kind']:13s} {b['name'] or b['lines'][0][:70]}")
