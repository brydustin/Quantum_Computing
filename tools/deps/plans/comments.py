"""Audit tick 16 (2026-10-27): the (* ... *) process comments inside proofs removed from the notes
theories.  Kept: the title header, (*<*)/(*>*) document markup, Day 1's note on the No_Cloning import."""
import os, re, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

KEEP = ("Title:", "No_Cloning is imported", "If bell_state = u")

def strip_block_comments(text):
    out, i, removed = [], 0, []
    while True:
        j = text.find("(*", i)
        if j < 0 or text.startswith("(*)", j) and False:
            out.append(text[i:]); break
        if text.startswith("(*)", j) or text.startswith("(*<*)", j) or text.startswith("(*>*)", j):
            out.append(text[i:j + 2]); i = j + 2; continue
        k = text.find("*)", j)
        assert k > 0
        body = text[j + 2:k]
        if any(s in body for s in KEEP):
            out.append(text[i:k + 2]); i = k + 2; continue
        removed.append(" ".join(body.split())[:70])
        ls = text.rfind("\n", 0, j) + 1
        le = text.find("\n", k + 2); le = len(text) if le < 0 else le
        if text[ls:j].strip() == "" and text[k + 2:le].strip() == "":
            out.append(text[i:ls]); i = min(le + 1, len(text))
        else:
            out.append(text[i:j].rstrip(" ") + ("" if text[k + 2:le].strip() == "" else " ")); i = k + 2
    return re.sub(r"\n{3,}", "\n\n", "".join(out)), removed

total = 0
for f in sorted(os.listdir(P)):
    if not (f.startswith("Day") and f.endswith(".thy")) and f != "Quantum_Channels.thy":
        continue
    src = head(f)
    new, removed = strip_block_comments(src)
    if removed:
        open(os.path.join(P, f), "w").write(new)
        total += len(removed)
        print(f"{f}: {len(removed)} removed"); [print("   ", r) for r in removed]
print("installed", total)
