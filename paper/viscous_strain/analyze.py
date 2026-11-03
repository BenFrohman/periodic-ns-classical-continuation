"""Summarize completed runs (only files ending with done=True). NUMERICS, NOT PROOFS."""
import json,glob,sys,numpy as np
D=sys.argv[1]; rows=[]
for p in sorted(glob.glob(D+'/*.jsonl')):
    L=[json.loads(l) for l in open(p)]
    if not L or not L[-1].get('done'): print('INCOMPLETE, skipped',p); continue
    rows.append((p.split('/')[-1],L[:-1]))
for name,L in rows:
    print(name)
    for r in L[::3]+[L[-1]]: print(f"  t={r['t']:.2e} nut={r['nut']:.2e} M={r['M']:.4f} S={r['Sinf']:.4f} ratio={r['ratio']:.4f} heat={r['heat_ratio']:.4f}")
    # fit ratio = a + b log(1/(nu t)) over t>0 where nu t K^2 > 1 (scales below sqrt(nu t) smoothed)
    K=L[0]['K']; P=[r for r in L if r['t']>0 and r['nut']*K*K>1]
    if len(P)>=3:
        x=np.log(1/np.array([r['nut'] for r in P])); y=np.array([r['ratio'] for r in P]); b,a=np.polyfit(x,y,1)
        yh=np.array([r['heat_ratio'] for r in P]); bh,ah=np.polyfit(x,yh,1)
        print(f"  fit (nu t K^2>1, n={len(P)}): NS ratio = {a:.3f} + {b:.3f} log(1/(nu t)); heat = {ah:.3f} + {bh:.3f} log(1/(nu t)); 1/pi={1/np.pi:.3f}")
# LaTeX tables (complete runs only)
T=open('tables.tex','w')
T.write("\\begin{center}\\small\\begin{tabular}{rrrrrr}$K$&$\\nu$&$n$&$a$&$b$&$b_{\\rm heat}$\\\\\\hline\n")
for name,L in rows:
    if name.startswith('amp'): continue
    K=L[0]['K']; P=[r for r in L if r['t']>0 and r['nut']*K*K>1]
    if len(P)<3: T.write(f"{K}&{L[0]['nu']:g}&{len(P)}&--&--&--\\\\\n"); continue
    x=np.log(1/np.array([r['nut'] for r in P])); b,a=np.polyfit(x,[r['ratio'] for r in P],1); bh,_=np.polyfit(x,[r['heat_ratio'] for r in P],1)
    T.write(f"{K}&{L[0]['nu']:g}&{len(P)}&{a:.3f}&{b:.3f}&{bh:.3f}\\\\\n")
T.write("\\end{tabular}\\end{center}\n")
T.write("\\begin{center}\\small\\begin{tabular}{rrrrr}$A$&$t$&$M(t)$&ratio&heat ratio\\\\\\hline\n")
for name,L in rows:
    if not name.startswith('amp'): continue
    for r in [L[0],L[len(L)//2],L[-1]]: T.write(f"{r['A']:g}&{r['t']:.4f}&{r['M']:.3f}&{r['ratio']:.3f}&{r['heat_ratio']:.3f}\\\\\n")
T.write("\\end{tabular}\\end{center}\n"); T.close()
