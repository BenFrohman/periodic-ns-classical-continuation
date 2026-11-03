"""Same statistics as paper/window_tests/analyze.py and paper/offset_tests/analyze.py, on JHTDB runs."""
import numpy as np, glob, sys
def lg(D):
    n = np.linalg.norm(D, axis=-1); return np.minimum(n, np.sqrt(np.clip(4-n**2, 0, None)))
def fitb(n, y):
    m = (n > 0) & (y > 1e-12); return np.polyfit(np.log(n[m]), np.log(y[m]), 1)[0]
for f in sorted(glob.glob(sys.argv[1] if len(sys.argv) > 1 else '/workspace/archive/jhtdb/*.npz')):
    z = np.load(f); D, S, H, off = z['D'], z['SEP'], z['INHI'], z['off']; dx = 2*np.pi/1024
    nW = D.shape[0]-1; n = np.arange(nW+1); G = lg(D)
    print(f"\n== {f.split('/')[-1]}  omega_ref={z['M'][0]:.1f}  high-set thr={float(z['thr']):.1f}  windows={nW}  t {z['T'][0]:.3f}->{z['T'][-1]:.3f}  pairs={len(off)}")
    print("window test: offset | beta(cum~n^beta) | cum/L1 | cum/L2 | lag1 corr signed | lag1 corr line incr | beta line gap | end median cum | frac pairs both-high at end")
    dk = np.diff(D, axis=0); dn = np.linalg.norm(dk, axis=2)
    for o in (1, 2, 4, 8):
        s = off == o; cum = np.linalg.norm(D[:, s]-D[0, s], axis=2)
        L1 = np.vstack([np.zeros(s.sum()), np.cumsum(dn[:, s], 0)]); L2 = np.sqrt(np.vstack([np.zeros(s.sum()), np.cumsum(dn[:, s]**2, 0)]))
        mc = np.median(cum, 1); a, b = dk[:-1, s], dk[1:, s]
        c = np.sum(a*b, 2).sum()/np.sqrt(np.sum(a*a, 2).sum()*np.sum(b*b, 2).sum())
        gi = np.diff(G[:, s], axis=0); cg = np.corrcoef(gi[:-1].ravel(), gi[1:].ravel())[0, 1]
        mg = np.median(np.abs(G[:, s]-G[0, s]), 1)
        print(f"  {o} | {fitb(n, mc):.2f} | {mc[-1]/np.median(L1[-1]):.3f} | {mc[-1]/np.median(L2[-1]):.2f} | {c:+.3f} | {cg:+.3f} | {fitb(n, mg):.2f} | {mc[-1]:.3f} | {H[-1, s].mean():.2f}")
    gk = np.abs(np.diff(G, axis=0)); r = S[:-1]; hi = H[:-1] & H[1:]
    def gam(mask):
        x, y = r[mask], gk[mask]; m = y > 1e-8; x, y = x[m], y[m]
        if len(x) < 100: return np.nan
        bins = np.quantile(x, np.linspace(0, 1, 11)); xs, ys = [], []
        for a_, b_ in zip(bins[:-1], bins[1:]):
            q = (x >= a_) & (x < b_)
            if q.sum() > 30: xs.append(np.median(x[q])); ys.append(np.median(y[q]))
        return np.polyfit(np.log(xs), np.log(ys), 1)[0] if len(xs) > 2 else np.nan
    Q = G/np.sqrt(S); Qd = G/np.sqrt(S/dx)
    print(f"offset test: gamma_all={gam(np.ones_like(hi)):.2f}  gamma_high={gam(hi):.2f} (n={hi.sum()})  median L=|d|/r high set={np.median(gk[hi]/r[hi]) if hi.sum() else np.nan:.2f} (r in box units)")
    print("  first-window median |d| by offset 1/2/4/8: " + "/".join(f"{np.median(gk[0, off == o]):.3f}" for o in (1, 2, 4, 8)))
    print("  Holder quotient G/sqrt(r) (box units) start / end / max-over-windows median, by offset:")
    for o in (1, 2, 4, 8):
        s = off == o; med = np.median(Q[:, s], 1)
        print(f"    {o}: {med[0]:.2f} / {med[-1]:.2f} / {med.max():.2f}   [grid units G/sqrt(r/dx): {np.median(Qd[0, s]):.3f} / {np.median(Qd[-1, s]):.3f}]   median sep growth {np.median(S[-1, s]/S[0, s]):.2f}x")
