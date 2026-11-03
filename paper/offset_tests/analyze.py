"""Small-separation gain: per-window line-direction drift vs separation r (offsets 1/2/4/8 cells)."""
import numpy as np, glob
def lg(D):
    n = np.linalg.norm(D, axis=-1); return np.minimum(n, np.sqrt(np.clip(4-n**2, 0, None)))
print("file | ||w||max | windows | gamma_all (|d_k| ~ r_k^gamma, binned medians, r<0.5) | gamma_high (both in high set) | first-window median |d| by offset 1/2/4/8 | median L=|d|/r (high set) | end Holder quotient G/sqrt(r) by offset | max over windows of median quotient, offset 1")
for f in sorted(glob.glob("N*.npz")):
    z = np.load(f); D, S, H, M, off, N = z["D"], z["SEP"], z["INHI"], z["M"], z["off"], int(z["N"])
    G = lg(D); dk = np.abs(np.diff(G, axis=0)); r = S[:-1]; hi = H[:-1] & H[1:]
    def gam(mask):
        x, y = r[mask], dk[mask]; m = (x < 0.5) & (y > 1e-8); x, y = x[m], y[m]
        bins = np.quantile(x, np.linspace(0, 1, 11)); xs, ys = [], []
        for a, b in zip(bins[:-1], bins[1:]):
            s = (x >= a) & (x < b)
            if s.sum() > 30: xs.append(np.median(x[s])); ys.append(np.median(y[s]))
        return np.polyfit(np.log(xs), np.log(ys), 1)[0] if len(xs) > 2 else np.nan
    first = [np.median(dk[0, off == o]) for o in (1, 2, 4, 8)]
    Lh = np.median(dk[hi]/r[hi]) if hi.sum() else np.nan
    Q = G/np.sqrt(S); endq = [np.median(Q[-1, off == o]) for o in (1, 2, 4, 8)]
    q1 = np.median(Q[:, off == 1], axis=1).max()
    print(f"{f[:-4]} | {M.max():.1f} | {D.shape[0]-1} | {gam(np.ones_like(hi)):.2f} | {gam(hi):.2f} (n={hi.sum()}) | "
          + "/".join(f"{v:.3f}" for v in first) + f" | {Lh:.2f} | " + "/".join(f"{v:.2f}" for v in endq) + f" | {q1:.2f}")
