# Lines (wc -l + 1) and results (lemma/theorem/corollary/proposition) per level of Part VI,
# as reported in the paper's Table of sizes and appendix.
import os, re
P = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEVELS = [
  ('Mathematics', 'Algorithms', ['Hermitian_Functional_Calculus', 'Phase_Estimation', 'QPE_Precision', 'QFT_Fourier', 'QPE_Register']),
  ('Algorithm', 'Algorithms', ['HHL', 'HHL_Trajectory', 'HHL_Approximate', 'HHL_Window', 'HHL_Simulation', 'HHL_Complete',
    'HHL_Filter', 'HHL_Filter_Bounds', 'HHL_Runtime', 'HHL_Reduction', 'HHL_Rectangular', 'HHL_Discussion', 'HHL_Optimality']),
  ('Program', 'Algorithms', ['QPE_Program', 'HHL_Program', 'HHL_Termination', 'HHL_Paper_Program', 'HHL_Gate_Refinements',
    'HHL_Preconditioned']),
  ('Circuit', 'Algorithms', ['HHL_Gates', 'HHL_Uniform_Rotation', 'HHL_State_Preparation', 'HHL_All_Elementary', 'HHL_Trotter',
    'HHL_Sparse_Split', 'HHL_Sparse_Circuit']),
]
EXTRA = [('Search bound', 'Search', ['HHL_Search_Bound']), ('Example run', 'Demo', ['HHL_Demo'])]

def count(d, t):
    s = open(os.path.join(P, d, t + '.thy')).read()
    return s.count('\n') + 1, len(re.findall(r'(?m)^\s*(lemma|theorem|corollary|proposition)\b', s))

listed = set()
tot = [0, 0, 0]
for name, d, ts in LEVELS + EXTRA:
    l = r = 0
    for t in ts:
        a, b = count(d, t); l += a; r += b; listed.add(t)
        print('  %-32s %6d %5d' % (t, a, b))
    print('%-34s %6d %5d  (%d theories)' % (name, l, r, len(ts)))
    if (name, d, ts) in LEVELS:
        tot[0] += len(ts); tot[1] += l; tot[2] += r
print('%-34s %6d %5d  (%d theories)' % ('Part VI', tot[1], tot[2], tot[0]))
missing = sorted(f[:-4] for f in os.listdir(os.path.join(P, 'Algorithms')) if f.endswith('.thy') and f[:-4] not in listed)
if missing: print('NOT IN ANY LEVEL:', ', '.join(missing))
