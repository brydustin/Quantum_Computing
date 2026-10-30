#!/usr/bin/env python3
"""Regenerate the bodies of the marked listings of paper_hhl from the theory sources.

A listing is marked by a comment line directly before it:
    %%LST <file> <name> [<name> ...]          statements of the named facts and definitions
    %%LST <file> --lines a-b [<name> ...]     a verbatim line range first (e.g. a context), then facts
The body between \\begin{lstlisting}[...] and \\end{lstlisting} is replaced by the output of
thy2lst.py.  Unmarked listings (abridged ones) are left alone.  Run from anywhere; edits in place.
"""
import glob, os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
PAPER = os.path.dirname(HERE)

def gen(args):
    out = subprocess.run([sys.executable, os.path.join(HERE, 'thy2lst.py')] + args,
                         capture_output=True, text=True)
    if out.returncode:
        raise SystemExit(f'thy2lst {" ".join(args)}: {out.stdout}{out.stderr}')
    return out.stdout.rstrip('\n').split('\n')

def main():
    changed = 0
    for fn in sorted(glob.glob(os.path.join(PAPER, '*.tex'))):
        L = open(fn).read().split('\n')
        out, i = [], 0
        while i < len(L):
            l = L[i]
            out.append(l)
            m = re.match(r'^%%LST\s+(.*)$', l)
            if m:
                j = i + 1
                while not L[j].lstrip().startswith(r'\begin{lstlisting}'):
                    out.append(L[j]); j += 1
                begin = j
                # the option list may span lines; it ends with ']'
                while not L[j].rstrip().endswith(']'):
                    j += 1
                out.extend(L[begin:j + 1])
                k = j + 1
                while not L[k].startswith(r'\end{lstlisting}'):
                    k += 1
                body = gen(m.group(1).split())
                if L[j + 1:k] != body:
                    changed += 1
                out.extend(body)
                out.append(L[k])
                i = k + 1
                continue
            i += 1
        open(fn, 'w').write('\n'.join(out))
    print(f'{changed} listing(s) regenerated')

if __name__ == '__main__':
    main()
