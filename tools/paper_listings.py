import re,glob,os
# Check every top-level item of the paper's Isabelle listings against the theory sources.
# Known non-matches: QHLProver syntax annotations (2) and the ⊗^n symbol (1); "..." marks an abridged item.
P=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
AFP=os.environ.get('AFP','/home/dusty/Desktop/Isabelle/afp-2026-04-09/thys')
inv = {
 r'\forall':'\\<forall>', r'\exists':'\\<exists>', r'\bigwedge':'\\<And>', r'\Longrightarrow':'\\<Longrightarrow>',
 r'\longrightarrow':'\\<longrightarrow>', r'\Rightarrow':'\\<Rightarrow>', r'\longleftrightarrow':'\\<longleftrightarrow>',
 r'\in':'\\<in>', r'\notin':'\\<notin>', r'\le':'\\<le>', r'\ge':'\\<ge>', r'\neq':'\\<noteq>', r'\wedge':'\\<and>',
 r'\vee':'\\<or>', r'\neg':'\\<not>', r'\lambda':'\\<lambda>', r'\sum':'\\<Sum>', r'\|':'\\<parallel>', r'|':'\\<bar>',
 r'\langle':'\\<langle>', r'\rangle':'\\<rangle>', r'\cdot':'\\<cdot>', r'\otimes':'\\<Otimes>', r'\dagger':'\\<dagger>',
 r'\theta':'\\<theta>', r'\kappa':'\\<kappa>', r'\eta':'\\<eta>', r'\varepsilon':'\\<epsilon>', r'\delta':'\\<delta>',
 r'\rho':'\\<rho>', r'\sigma':'\\<sigma>', r'\varphi':'\\<phi>', r'\psi':'\\<psi>', r'\Phi':'\\<Phi>', r'\Psi':'\\<Psi>',
 r'\vdash':'\\<turnstile>', r'\models':'\\<Turnstile>', r'\equiv':'\\<equiv>', r'\Delta':'\\<Delta>', r'\lceil':'\\<lceil>', r'\rceil':'\\<rceil>',
}
def unesc(t):
    # ~$...$~ blocks
    def rep(m):
        x=m.group(1)
        x=re.sub(r'_\{(.*?)\}', lambda mm: '\\<^sub>'+mm.group(1), x)
        x=re.sub(r'\^\{(.*?)\}', lambda mm: '\\<^sup>'+mm.group(1), x)
        for k in sorted(inv, key=len, reverse=True):
            x=x.replace(k, inv[k])
        x=x.replace('\\<^sup>\\<dagger>','\\<^sup>\\<dagger>')
        return x
    t=t.replace('~\\$\\$~','$$')
    t=re.sub(r'~\$(.*?)\$~', rep, t)
    return t
def norm(s):
    s=s.replace('Matrix.mat','mat').replace('Matrix.vec','vec').replace('Quantum_Computing_3_10.hermitian','hermitian')
    s=s.replace('Quantum.unitary','unitary').replace('Complex_Matrix.unitary','unitary')
    return re.sub(r'\s+',' ',s).strip()
srcs={}
for d in ['Algorithms','Day11','Demo','.']:
    for f in glob.glob(os.path.join(P,d,'*.thy')):
        if os.path.basename(f) in ('Quantum_Computing.thy','Quantum_Computing_OLD.thy'): continue
        srcs[f]=norm(open(f).read())
qhl=norm(open(os.path.join(AFP,'QHLProver/Quantum_Hoare.thy')).read())
for fn in [os.path.join(P,'paper/paper.tex')]:
    L=open(fn).read().split('\n'); i=0
    while i<len(L):
        if L[i].startswith('\\begin{lstlisting}'):
            j=i
            while not L[j].rstrip().endswith(']'): j+=1
            k=j+1; body=[]
            while not L[k].startswith('\\end{lstlisting}'): body.append(L[k]); k+=1
            # split into items at top-level keywords
            items=[]; cur=[]
            for b in body:
                if re.match(r'^(theorem|lemma|corollary|definition|abbreviation|primrec|context|begin|fixes|assumes|value)\b', b) and cur and not b.startswith(('fixes','assumes')):
                    items.append(cur); cur=[]
                cur.append(b)
            if cur: items.append(cur)
            for it in items:
                txt=norm(unesc('\n'.join(it)))
                if '...' in txt or '(*' in txt: 
                    print('SKIP(abridged)', os.path.basename(fn), txt[:60]); continue
                ok=any(txt in s for s in srcs.values()) or txt in qhl
                if not ok:
                    # find longest matching prefix for diagnostics
                    best=0
                    for s in list(srcs.values())+[qhl]:
                        lo,hi=0,len(txt)
                        while lo<hi:
                            mid=(lo+hi+1)//2
                            if txt[:mid] in s: lo=mid
                            else: hi=mid-1
                        best=max(best,lo)
                    print('MISMATCH', os.path.basename(fn), '| matched:', txt[:best][-60:], '| then:', txt[best:best+70])
                else:
                    print('ok', os.path.basename(fn), txt[:50])
            i=k
        i+=1
