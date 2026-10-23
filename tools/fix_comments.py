# Make the text of \<comment> cartouches LaTeX-safe when proofs are typeset: words that contain
# characters LaTeX treats specially (or Isabelle symbols, which comments emit raw) are wrapped in
# nested cartouches.  Usage: python3 tools/fix_comments.py [--write] FILE...
import re, sys
OPEN, CLOSE = '\\<open>', '\\<close>'
SPECIAL = re.compile(r'[_^#%&$~{}\\]')
def split_top(body):
    # list of (is_cartouche, text) at nesting depth 0 of body
    out, i, depth, cur = [], 0, 0, ''
    while i < len(body):
        if body.startswith(OPEN, i):
            if depth == 0 and cur: out.append((False, cur)); cur = ''
            depth += 1; cur += OPEN; i += len(OPEN); continue
        if body.startswith(CLOSE, i):
            depth -= 1; cur += CLOSE; i += len(CLOSE)
            if depth == 0: out.append((True, cur)); cur = ''
            continue
        cur += body[i]; i += 1
    if cur: out.append((depth > 0, cur))
    return out
def fix_word(w):
    if not SPECIAL.search(w): return w
    m = re.match(r'^([(\[]*)(.*?)([.,;:)\]]*)$', w, re.S)
    a, core, b = m.groups()
    core = core.replace('\\_', '_')
    if not core: return w
    return a + OPEN + core + CLOSE + b
TOKEN = re.compile(r'(\$[^$]*\$)|@?\{(?:term|thm|const|typ|text)\s+(?:"([^"]*)"|([^}]*))\}')
def fix_text(t):
    # $...$ is LaTeX and kept; antiquotations become cartouches; other words are wrapped if needed
    res, i = '', 0
    for m in TOKEN.finditer(t):
        res += words(t[i:m.start()])
        res += m.group(1) if m.group(1) else OPEN + (m.group(2) if m.group(2) is not None else m.group(3)).strip() + CLOSE
        i = m.end()
    return res + words(t[i:])
def words(t):
    return ''.join(fix_word(x) if not x.isspace() else x for x in re.split(r'(\s+)', t))
def fix_body(body):
    res = ''
    for cart, t in split_top(body):
        res += t if cart else fix_text(t)
    return res
def process(s):
    out, i, n = '', 0, 0
    key = '\\<comment> ' + OPEN
    while True:
        j = s.find(key, i)
        if j < 0: return out + s[i:], n
        k, depth = j + len(key), 1
        while depth:
            if s.startswith(OPEN, k): depth += 1; k += len(OPEN)
            elif s.startswith(CLOSE, k): depth -= 1; k += len(CLOSE)
            else: k += 1
        body = s[j + len(key):k - len(CLOSE)]
        nb = fix_body(body)
        if nb != body: n += 1
        out += s[i:j] + key + nb + CLOSE; i = k
w = '--write' in sys.argv
tot = 0
for f in [a for a in sys.argv[1:] if a != '--write']:
    s = open(f).read(); t, n = process(s)
    if n: print(f, n); tot += n
    if w and t != s: open(f, 'w').write(t)
print('total', tot)
