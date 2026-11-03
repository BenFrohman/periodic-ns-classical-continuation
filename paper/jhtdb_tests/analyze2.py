"""Run-2 analysis (t0 = 1,3,5,7,9; offsets 1..32 cells), statistics restricted to the high set
(both points |omega| >= thr at both ends of a window). eta ~ 0.00287 ~ dx/2.14."""
import numpy as np, glob
dx = 2*np.pi/1024; OFFS = (1, 2, 4, 8, 16, 32)
def lg(D):
    n = np.linalg.norm(D, axis=-1); return np.minimum(n, np.sqrt(np.clip(4-n**2, 0, None)))
def fitb(n, y):
    m = (n > 0) & (y > 1e-12); return np.polyfit(np.log(n[m]), np.log(y[m]), 1)[0] if m.sum() > 3 else np.nan
rows = []
for f in sorted(glob.glob('/workspace/archive/jhtdb/r2_t*.npz')):
    if 'ckpt' in f or 'seed' in f: continue
    z = np.load(f); D, S, H, off = z['D'], z['SEP'], z['INHI'], z['off']; G = lg(D)
    gk = np.abs(np.diff(G, axis=0)); r = S[:-1]; hi = H[:-1] & H[1:]; nW = D.shape[0]-1
    print(f"\n== t0={z['T'][0]:.1f} omega_ref={z['M'][0]:.1f} thr={float(z['thr']):.1f} windows={nW} (t->{z['T'][-1]:.3f})")
    print(" offset(cells) | r/eta | high-set window-samples | median high-set |d_k| | median L=|d|/r | local gamma to next offset | high-set Holder quotient G/sqrt(r) first/last-third median | beta(cum, pairs high at start)")
    meds = []
    for o in OFFS:
        s = (off == o)[None, :] & hi
        meds.append(np.median(gk[s]/1.0) if s.sum() else np.nan)
    for i, o in enumerate(OFFS):
        s = (off == o)[None, :] & hi; Q = (G[:-1]/np.sqrt(S[:-1]))
        third = nW//3; q1 = Q[:third][s[:third]]; q3 = Q[-third:][s[-third:]]
        gam = np.log(meds[i+1]/meds[i])/np.log(2) if i+1 < len(OFFS) else np.nan
        sp = off == o; cum = np.median(np.linalg.norm(D[:, sp]-D[0, sp], axis=2), 1)
        print(f"  {o:2d} | {o*dx/0.00287:5.1f} | {s.sum():5d} | {meds[i]:.4f} | {np.median(gk[s]/r[s]) if s.sum() else np.nan:.2f} | {gam:+.2f} | "
              f"{(np.median(q1) if len(q1) else np.nan):.2f} / {(np.median(q3) if len(q3) else np.nan):.2f} (n={len(q1)}/{len(q3)}) | {fitb(np.arange(nW+1), cum):.2f}")
