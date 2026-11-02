"""Window-drift cancellation analysis. Window k ends where int ||w||_inf dt crosses k."""
import numpy as np, glob
def fit(n, y):
    m = (n > 0) & (y > 1e-12); return np.polyfit(np.log(n[m]), np.log(y[m]), 1)[0]
print("file | windows | ||w||max | offset | pairs | median beta(cum ~ n^beta) | cum/L1 at end | cum/L2 at end | lag1 corr(signed) | lag1 corr(|line incr|) | beta line-gap | median end |dtau|/sqrt(r)")
for f in sorted(glob.glob("N*.npz")):
    z = np.load(f); D = z["D"]; S = z["SEP"]; H = z["INHI"]; M = z["M"]
    nW = D.shape[0]; n = np.arange(nW)
    nd = np.linalg.norm(D, axis=2); G = np.minimum(nd, np.sqrt(np.clip(4 - nd**2, 0, None)))
    dk = np.diff(D, axis=0); dn = np.linalg.norm(dk, axis=2)
    for off in (1, 4):
        sel = z["off"] == off; stay = H[:, sel].mean()
        cum = np.linalg.norm(D[:, sel] - D[0, sel], axis=2)
        L1 = np.vstack([np.zeros(sel.sum()), np.cumsum(dn[:, sel], 0)])
        L2 = np.sqrt(np.vstack([np.zeros(sel.sum()), np.cumsum(dn[:, sel]**2, 0)]))
        mc, m1, m2 = np.median(cum, 1), np.median(L1, 1), np.median(L2, 1)
        a, b = dk[:-1, sel], dk[1:, sel]
        c = np.sum(a*b, 2).sum() / np.sqrt(np.sum(a*a, 2).sum()*np.sum(b*b, 2).sum())
        gi = np.diff(G[:, sel], axis=0); cg = np.corrcoef(gi[:-1].ravel(), gi[1:].ravel())[0, 1]
        mg = np.median(np.abs(G[:, sel] - G[0, sel]), 1)
        hq = np.median(G[-1, sel]/np.sqrt(S[-1, sel]))
        print(f"{f[:-4]} | {nW-1} | {M.max():.1f} | {off} | {sel.sum()} (high-set frac {stay:.2f}) | {fit(n, mc):.2f} | {mc[-1]/m1[-1]:.3f} | {mc[-1]/m2[-1]:.2f} | {c:+.3f} | {cg:+.3f} | {fit(n, mg):.2f} | {hq:.3f} (start {np.median(G[0,sel]/np.sqrt(S[0,sel])):.3f})")
