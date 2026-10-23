# Repoint the paper's source links (\repo and \isalink{file}{line}) to a commit (default HEAD).
# Each linked line is looked up at the old commit and found again at the new one (nearest
# identical line), following renames between the two commits; links into files absent from the
# old commit are kept.
import os, re, subprocess, sys
P = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(P)
tex = 'paper/paper.tex'
s = open(tex).read()
m = re.search(r'\\newcommand\{\\repo\}\{https://github.com/[^/]+/[^/]+/blob/([0-9a-f]+)\}', s)
old = m.group(1)
new = subprocess.check_output(['git', 'rev-parse', sys.argv[1] if len(sys.argv) > 1 else 'HEAD']).decode().strip()
renames = {}
for l in subprocess.check_output(['git', 'diff', '-M', '--name-status', old, new]).decode().split('\n'):
    p = l.split('\t')
    if p[0].startswith('R'): renames[p[1]] = p[2]
cache = {}
def lines(rev, f):
    if (rev, f) not in cache:
        try:
            cache[(rev, f)] = subprocess.check_output(['git', 'show', '%s:%s' % (rev, f)], stderr=subprocess.DEVNULL).decode().split('\n')
        except subprocess.CalledProcessError:
            cache[(rev, f)] = None
    return cache[(rev, f)]
bad = []
def fix(mm):
    f, l = mm.group(1), int(mm.group(2))
    nf = renames.get(f, f)
    o, n = lines(old, f), lines(new, nf)
    if n is None: bad.append('%s missing at %s' % (nf, new[:7])); return mm.group(0)
    if o is None: return mm.group(0)
    idx = [i + 1 for i, x in enumerate(n) if x == o[l - 1]]
    if not idx: bad.append('%s:%d line not found' % (f, l)); return mm.group(0)
    b = min(idx, key=lambda i: abs(i - l))
    if b != l or nf != f: print('moved %s:%d -> %s:%d' % (f, l, nf, b))
    return '\\isalink{%s}{%d}' % (nf, b)
s = re.sub(r'\\isalink\{([^}]*)\}\{(\d+)\}', fix, s)
s = s.replace('/blob/' + old + '}', '/blob/' + new + '}')
open(tex, 'w').write(s)
print('links at', new[:7], '(were', old[:7] + ')')
for b in bad: print('PROBLEM', b)
sys.exit(1 if bad else 0)
