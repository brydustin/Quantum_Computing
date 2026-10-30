#!/usr/bin/env python3
"""Print the statement of a named fact or definition, converted to the paper's listing syntax.

Usage: thy2lst.py FILE NAME [NAME ...]   (FILE relative to the repository root)
The statement runs from its keyword to the line before the proof; symbols become ~$...$~ escapes,
and lines are wrapped at whitespace.  Paste the output between \\begin{lstlisting} and \\end{lstlisting}.
"""
import re, sys, os

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SYM = {
    'forall': r'\forall', 'exists': r'\exists', 'And': r'\bigwedge', 'Longrightarrow': r'\Longrightarrow',
    'longrightarrow': r'\longrightarrow', 'Rightarrow': r'\Rightarrow', 'longleftrightarrow': r'\longleftrightarrow',
    'in': r'\in', 'notin': r'\notin', 'le': r'\le', 'ge': r'\ge', 'noteq': r'\neq', 'and': r'\wedge',
    'or': r'\vee', 'not': r'\neg', 'lambda': r'\lambda', 'Sum': r'\sum', 'parallel': r'\|', 'bar': '|',
    'langle': r'\langle', 'rangle': r'\rangle', 'cdot': r'\cdot', 'Otimes': r'\otimes', 'dagger': r'\dagger',
    'times': r'\times', 'theta': r'\theta', 'kappa': r'\kappa', 'eta': r'\eta', 'epsilon': r'\varepsilon',
    'delta': r'\delta', 'rho': r'\rho', 'sigma': r'\sigma', 'phi': r'\varphi', 'psi': r'\psi', 'Phi': r'\Phi',
    'Psi': r'\Psi', 'turnstile': r'\vdash', 'Turnstile': r'\models', 'equiv': r'\equiv', 'Delta': r'\Delta',
    'lceil': r'\lceil', 'rceil': r'\rceil', 'mu': r'\mu', 'alpha': r'\alpha', 'beta': r'\beta',
    'lambda_': r'\lambda', 'Lambda': r'\Lambda', 'pi': r'\pi', 'tau': r'\tau', 'omega': r'\omega',
    'Omega': r'\Omega', 'chi': r'\chi', 'gamma': r'\gamma', 'Gamma': r'\Gamma', 'zeta': r'\zeta',
    'circ': r'\circ', 'subseteq': r'\subseteq', 'inter': r'\cap', 'union': r'\cup', 'infinity': r'\infty',
    'oslash': r'\oslash', 'otimes': r'\otimes', 'Sqinter': r'\bigsqcap', 'lbrakk': r'\llbracket', 'rbrakk': r'\rrbracket',
    'Rightarrow_': r'\Rightarrow', 'rightleftharpoons': r'\rightleftharpoons', 'leftarrow': r'\leftarrow', 'mapsto': r'\mapsto', 'odot': r'\odot',
}

def statement(src, name):
    lines = src.split('\n')
    pat = re.compile(r'^\s*(lemma|theorem|corollary|proposition|definition|fun|abbreviation|lift_definition|inductive)\s+' + re.escape(name) + r'\b')
    for i, l in enumerate(lines):
        if pat.match(l):
            out = [l]
            for m in lines[i + 1:]:
                s = m.strip()
                if not s or s.startswith('(*'):
                    break
                if re.match(r'^(proof|by|using|unfolding|apply|including|supply|\.\.|\.)\b', s) or s.startswith('proof') \
                        or re.match(r'^(lemma|theorem|corollary|definition|fun|text|section|subsection|end)\b', s):
                    break
                out.append(m)
            # 'definition ... where "..."': keep through the defining equation
            while out and not out[-1].strip():
                out.pop()
            return out
    raise SystemExit(f'{name}: not found')

def conv(text):
    # U \<approx>\<^bsub>e\<^esub> V
    def close(m):
        e = m.group(1).replace('_', r'\_').replace('\\<^sup>2', r'\textsuperscript{2}').replace('^', r'\textasciicircum{}')
        e = re.sub(r'\\<bar>', '$|$', e)
        return '~\\closeto{' + e + '}~'
    text = re.sub(r'\\<approx>\\<\^bsub>(.*?)\\<\^esub>', close, text)
    text = text.replace('$$', '~\\$\\$~')          # matrix indexing, not math
    text = text.replace('\\<open>', '"').replace('\\<close>', '"')
    def symsup(m):
        k = m.group(2)
        if k not in SYM:
            raise SystemExit(f'unknown symbol \\<{k}>')
        return '~$' + ('^' if m.group(1) == 'sup' else '_') + '{' + SYM[k] + '}$~'
    text = re.sub(r'\\<\^(sup|sub)>\\<([A-Za-z]+)>', symsup, text)
    text = re.sub(r'\\<\^bsup>(.*?)\\<\^esup>', lambda m: '~$^{' + m.group(1) + '}$~', text)
    def sub(m):
        return '~$_{' + m.group(1) + '}$~'
    text = re.sub(r'\\<\^sub>([A-Za-z0-9]+)', sub, text)
    text = re.sub(r'\\<\^sup>([A-Za-z0-9\\<>]+?)(?=[^A-Za-z0-9]|$)', lambda m: '~$^{' + m.group(1) + '}$~', text)
    def sym(m):
        k = m.group(1)
        if k not in SYM:
            raise SystemExit(f'unknown symbol \\<{k}>')
        return '~$' + SYM[k] + '$~'
    text = re.sub(r'\\<([A-Za-z]+)>', sym, text)
    # merge adjacent escapes: ~$a$~~$b$~ -> ~$a b$~
    text = re.sub(r'\$~~\$', '', text)
    return text

def vis(t):
    """Printed width: an escape ~$...$~ prints as about one character."""
    return len(re.sub(r'~\$.*?\$~', 'xx', t))

def atoms(text):
    """Split at spaces, keeping each ~...~ escape whole (it must not be broken across lines)."""
    out, buf = [], None
    for t in text.split(' '):
        if buf is not None:
            buf += ' ' + t
            if t.count('~') % 2 == 1:
                out.append(buf); buf = None
        elif t.count('~') % 2 == 1:
            buf = t
        else:
            out.append(t)
    if buf is not None:
        out.append(buf)
    return out

def wrap(line, width=72):
    if vis(line) <= width:
        return [line]
    ind = len(line) - len(line.lstrip())
    words, out, cur = atoms(line.strip()), [], ' ' * ind
    for w in words:
        cand = (cur + ' ' + w) if cur.strip() else cur + w
        if vis(cand) > width and cur.strip():
            out.append(cur)
            cur = ' ' * (ind + 4) + w
        else:
            cur = cand
    out.append(cur)
    return out

def reflow_context(lines):
    out = []
    for l in lines:
        t = ' '.join(l.split())
        if t in ('context', 'begin') or not out:
            out.append(t)
        elif t.split(' ')[0] in HEADS:
            out.append('  ' + t)
        elif t.startswith('and '):
            out.append('    ' + t)
        else:
            out[-1] += ' ' + t
    return out

HEADS = ('fixes', 'assumes', 'shows', 'defines', 'obtains', 'where')

def reflow(lines):
    """One logical line per clause: keyword lines and quoted lines start a line, others are joined."""
    out = []
    for i, l in enumerate(lines):
        t = ' '.join(l.split())
        if i == 0:
            out.append(t)
        elif t.split(' ')[0] in HEADS or t.startswith('"'):
            out.append('  ' + t)
        elif t.startswith('and '):
            out.append('    ' + t)
        elif t.startswith('| '):
            out.append(t)
        else:
            out[-1] += ' ' + t
    return out

def main():
    f, names = sys.argv[1], sys.argv[2:]
    src = open(os.path.join(ROOT, f)).read()
    if names and names[0] == '--lines':          # verbatim line range a-b (1-based, inclusive)
        a, b = map(int, names[1].split('-'))
        for l in reflow_context(src.split('\n')[a - 1:b]):
            for w in wrap(conv(l)):
                print(w)
        names = names[2:]
    for n in names:
        for l in reflow(statement(src, n)):
            for w in wrap(conv(l)):
                print(w)

if __name__ == '__main__':
    main()
