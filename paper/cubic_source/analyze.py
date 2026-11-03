"""Summarise cubic-source runs (NUMERICS, NOT PROOFS). Usage: python3 analyze.py /workspace/archive/cubic_source/*.jsonl"""
import json, sys, numpy as np
print("run | snaps | M range | max sig/M^3 | max ||S||/M | max ||S||/(M logfac) | max visc/M^2 | kappa_proxy(top M quartile) min/med | slope log(sig/M^3) vs log M")
for f in sys.argv[1:]:
    R = [json.loads(l) for l in open(f)]
    M = np.array([r['M'] for r in R]); s3 = np.array([r['sig_M3'] for r in R]); Sm = np.array([r['Sinf_M'] for r in R])
    Sl = np.array([r['Sinf_Mlog'] for r in R]); v = np.array([r['visc_M2'] for r in R])
    C = s3.max()                         # empirical C for this run
    kap = (C*M**3 - s3*M**3)/M**4         # (C M^3 - sigma)/M^4 >= 0 by construction
    top = M >= np.quantile(M, 0.75)
    pos = s3 > 0
    sl = np.polyfit(np.log(M[pos]), np.log(s3[pos]), 1)[0] if pos.sum() > 3 else float('nan')
    sk = np.polyfit(np.log(M[top]), np.log(np.maximum(kap[top], 1e-12)), 1)[0]
    print(f"{f.split('/')[-1][:-6]} | {len(R)} | {M.min():.1f}-{M.max():.1f} | {C:.3f} | {Sm.max():.3f} | {Sl.max():.3f} | {v.max():.4f} | {kap[top].min():.2e}/{np.median(kap[top]):.2e} (slope vs M {sk:.2f}) | {sl:.2f}")

# LaTeX table + summary
rows=[]
for f in sys.argv[1:]:
    R=[json.loads(l) for l in open(f)]
    M=np.array([r['M'] for r in R]); s3=np.array([r['sig_M3'] for r in R]); Sm=np.array([r['Sinf_M'] for r in R]); v=np.array([r['visc_M2'] for r in R])
    pos=s3>0; sl=np.polyfit(np.log(M[pos]),np.log(s3[pos]),1)[0]
    C=s3.max(); kap=(C-s3)/M; top=M>=np.quantile(M,.75)
    n=f.split('/')[-1][:-6].split('_')
    rows.append(f"{n[0][1:]} & {n[1][2:]} & {n[2][1:]} & {len(R)*0.05:.2f} & {M.min():.1f}--{M.max():.1f} & {s3.min():.3f}--{C:.3f} & {sl:.2f} & {Sm.min():.2f}--{Sm.max():.2f} & {v.min():.4f} & {kap[top].min():.1e} \\\\")
open('numerics_table.tex','w').write("\\begin{center}\\small\\begin{tabular}{rrrrrrrrrr}\n$N$&$\\nu$&seed&$t_{\\max}$&$M$&$\\sigma/M^3$&slope&$\\|S\\|_\\infty/M$&min visc$/M^2$&min $\\kappa_{\\rm eff}$\\\\\\hline\n"+"\n".join(rows)+"\n\\end{tabular}\\end{center}\n")
