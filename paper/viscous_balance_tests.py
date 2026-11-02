"""Numerical test of smoothing versus drift in the viscous part of D tau/Dt on T^3.
These are NUMERICS, NOT PROOFS. Author: Benjamin Stanley Frohman.

Notation: omega = m tau with m = |omega| and P = I - tau(x)tau.
The viscous direction term is P Delta omega / m = P Delta tau + 2 (grad log m . grad) tau.
  smoothing S = P Delta tau = P Delta omega/m - drift
  drift     D = 2 (grad log m . grad) tau, with (grad tau)_ij = (d_j w_i - tau_i tau.d_j w)/m
Both are computed from spectral derivatives of omega, which is smooth, so tau is never differentiated
across zeros of omega. The Bochner balance compares |grad tau|^4 with |grad^2 tau|^2; grad^2 tau is
taken by central differences of grad tau, which is an approximation.
Two-point test: G(x,y) = 1 - <tau x, tau y>^2, the squared line gap. Its viscous rate is
  dG = -2 <tx,ty> (<V(x),ty> + <tx,V(y)>)
with V = S or D, at the sampled high-set pair that maximises G/|x-y|.
"""
import numpy as np, sys
rng = np.random.default_rng(0)
MODE = sys.argv[1] if len(sys.argv) > 1 and not sys.argv[1].isdigit() else 'basic'
if MODE == 'scale':   # python viscous_balance_tests.py scale N nu seed T wallclock_s
    N = int(sys.argv[2]); rng = np.random.default_rng(int(sys.argv[4]))
elif MODE == 'fit':
    N = 8
else:
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 64
L = 2*np.pi; x = np.arange(N)*L/N
X, Y, Z = np.meshgrid(x, x, x, indexing='ij')
k1 = np.fft.fftfreq(N, 1/N); KX, KY, KZ = np.meshgrid(k1, k1, k1, indexing='ij')
K = [KX, KY, KZ]; K2 = KX**2+KY**2+KZ**2; K2s = np.where(K2 == 0, 1, K2)
dealias = (np.abs(KX) < N/3) & (np.abs(KY) < N/3) & (np.abs(KZ) < N/3)
fft, ifft = np.fft.fftn, lambda a: np.real(np.fft.ifftn(a))

def curl_hat(uh):
    return [1j*(K[1]*uh[2]-K[2]*uh[1]), 1j*(K[2]*uh[0]-K[0]*uh[2]), 1j*(K[0]*uh[1]-K[1]*uh[0])]

def project(uh):
    d = (K[0]*uh[0]+K[1]*uh[1]+K[2]*uh[2])/K2s
    return [uh[i]-K[i]*d for i in range(3)]

def diagnostics(uh, theta=0.5, npairs=1000000, h=8):
    wh = curl_hat(uh); w = np.array([ifft(a) for a in wh])
    dw = np.array([[ifft(1j*K[j]*wh[i]) for j in range(3)] for i in range(3)])  # dw[i,j] = d_j w_i
    lw = np.array([ifft(-K2*wh[i]) for i in range(3)])
    m = np.sqrt((w**2).sum(0)); mmax = m.max(); hi = m >= theta*mmax
    t = w/np.maximum(m, 1e-300)
    tdw = np.einsum('i...,ij...->j...', t, dw)            # tau . d_j w  (= d_j m)
    gt = (dw - t[:, None]*tdw[None])/m                    # grad tau [i,j]
    glogm = tdw/m
    D = 2*np.einsum('j...,ij...->i...', glogm, gt)
    Plw = lw - t*np.einsum('i...,i...->...', t, lw)
    S = Plw/m - D
    nS = np.sqrt((S**2).sum(0))[hi]; nD = np.sqrt((D**2).sum(0))[hi]
    r = nD/np.maximum(nS, 1e-300)
    g2 = (gt**2).sum((0, 1))
    hess2 = np.zeros_like(m)
    for kk in range(3):
        d = (np.roll(gt, -1, axis=2+kk)-np.roll(gt, 1, axis=2+kk))/(2*L/N)
        hess2 += (d**2).sum((0, 1))
    q = (g2**2)[hi]/np.maximum(hess2[hi], 1e-300)
    # two-point test: pairs inside the high set, offsets up to h cells
    idx = np.argwhere(hi); n = len(idx)
    a = idx[rng.integers(0, n, npairs)]; off = rng.integers(-h, h+1, (npairs, 3))
    b = (a+off) % N; ok = hi[b[:, 0], b[:, 1], b[:, 2]] & (np.abs(off).sum(1) > 0)
    a, b, off = a[ok], b[ok], off[ok]
    ta = t[:, a[:, 0], a[:, 1], a[:, 2]].T; tb = t[:, b[:, 0], b[:, 1], b[:, 2]].T
    c = (ta*tb).sum(1); G = 1-c**2; dist = np.linalg.norm(off, axis=1)*L/N
    j = np.argmax(G/dist); A, B = np.array(a[j]), np.array(b[j])
    def qv(A, B):
        o = (B-A+N//2) % N - N//2
        if not (hi[tuple(A)] and hi[tuple(B)]) or not o.any(): return -1.0
        cc = t[(slice(None),)+tuple(A)] @ t[(slice(None),)+tuple(B)]
        return (1-cc**2)/(np.linalg.norm(o)*L/N)
    best = qv(A, B); moves = [np.eye(3, dtype=int)[k]*sg for k in range(3) for sg in (1, -1)]
    improved = True
    while improved:   # local maximisation over both points (discrete interior max)
        improved = False
        for which in (0, 1):
            for mv in moves:
                A2, B2 = ((A+mv) % N, B) if which == 0 else (A, (B+mv) % N)
                v = qv(A2, B2)
                if v > best + 1e-15: A, B, best, improved = A2, B2, v, True
    A, B = tuple(A), tuple(B); txA = t[(slice(None),)+A]; tyB = t[(slice(None),)+B]
    cj = txA @ tyB
    class _C: pass
    G = np.array([1-cj**2]); j = 0; c = np.array([cj]); ta = txA[None]; tb = tyB[None]
    def rate(V):
        return -2*c[j]*(V[(slice(None),)+A] @ tb[j] + ta[j] @ V[(slice(None),)+B])
    sm = rate(S); dr = rate(D)
    return dict(mmax=mmax, nhi=int(hi.sum()), r_max=r.max(), r_med=np.median(r),
                frac_drift_gt_smooth=(r > 1).mean(), q_max=q.max(), q_med=np.median(q),
                pairG=G[j], tp_smooth=sm, tp_drift=dr, tp_total=sm+dr)

def show(name, d):
    print(f"{name:28s} |w|max={d['mmax']:.3g} nhi={d['nhi']} drift/smooth max={d['r_max']:.3g} "
          f"med={d['r_med']:.3g} P(drift>smooth)={d['frac_drift_gt_smooth']:.2f} | "
          f"|grad tau|^4/|grad^2 tau|^2 max={d['q_max']:.3g} med={d['q_med']:.3g} | two-point G*={d['pairG']:.3g} "
          f"dG_visc/nu: smooth={d['tp_smooth']:+.3g} drift={d['tp_drift']:+.3g} total={d['tp_total']:+.3g}")

def random_field(kpeak=4, amp=1.0, M=24):
    # random modes drawn on a fixed M^3 wavenumber grid and embedded, so the same seed gives
    # the same datum at every N >= M (needed for the resolution-convergence check)
    km = np.fft.fftfreq(M, 1/M).astype(int)
    uh = []
    for _ in range(3):
        r = rng.standard_normal((M,)*3)+1j*rng.standard_normal((M,)*3)
        a = np.zeros((N,)*3, complex); a[np.ix_(km % N, km % N, km % N)] = r
        uh.append(a*np.exp(-(np.sqrt(K2)-kpeak)**2/2))
    uh = project([fft(ifft(a)) for a in uh]); uh = [a*dealias for a in uh]
    e = sum((np.abs(a)**2).sum() for a in uh)/N**6
    return [a*amp/np.sqrt(e) for a in uh]

def ns_rhs_factory(nu):
    def rhs(uh):
        u = [ifft(a) for a in uh]; w = [ifft(a) for a in curl_hat(uh)]
        nl = [u[1]*w[2]-u[2]*w[1], u[2]*w[0]-u[0]*w[2], u[0]*w[1]-u[1]*w[0]]
        nlh = project([fft(a)*dealias for a in nl])
        return [nlh[i]-nu*K2*uh[i] for i in range(3)]
    return rhs

def scale_run(nu, seed, T, wall):
    import json, time
    t0 = time.time(); rhs = ns_rhs_factory(nu)
    uh = random_field(kpeak=3, amp=1.0); tnow, nextout = 0.0, 0.0
    while tnow <= T+1e-9 and time.time()-t0 < wall:
        if tnow >= nextout-1e-9:
            ens = sum((np.abs(a)**2).sum() for a in curl_hat(uh))/N**6
            eta = (nu**3/max(nu*ens, 1e-30))**0.25   # Kolmogorov scale, eps = nu <|w|^2>
            rec = dict(N=N, nu=nu, seed=seed, t=round(tnow, 4), enstrophy=ens, kmax_eta=(N/3)*eta)
            for th in (0.5, 0.7):
                d = diagnostics(uh, theta=th); rec.update({f"{k}_{th}": float(v) for k, v in d.items()})
            print(json.dumps(rec), flush=True); nextout += 0.25
        umax = max(np.abs(ifft(a)).max() for a in uh); dt = min(0.4*(L/N)/umax, 0.02)
        k1_ = rhs(uh); k2_ = rhs([uh[i]+dt/2*k1_[i] for i in range(3)])
        k3_ = rhs([uh[i]+dt/2*k2_[i] for i in range(3)]); k4_ = rhs([uh[i]+dt*k3_[i] for i in range(3)])
        uh = [uh[i]+dt/6*(k1_[i]+2*k2_[i]+2*k3_[i]+k4_[i]) for i in range(3)]; tnow += dt

def fit(paths):
    import json
    R = [json.loads(l) for p in paths for l in open(p) if l.startswith('{')]
    print(f"{len(R)} snapshots. NUMERICS, NOT PROOFS.")
    def pl(xs, ys):
        xs, ys = np.log(xs), np.log(ys)
        if len(xs) < 4: return float('nan'), float('nan')
        p, cov = np.polyfit(xs, ys, 1, cov=True); return p[0], np.sqrt(cov[0, 0])
    groups = sorted({(r['N'], r['nu']) for r in R})
    for th in (0.5, 0.7):
        print(f"\n== theta={th}: power-law fits ratio ~ |w|max^p over snapshots with t>=0.5 ==")
        for g in groups + [('all', None)]:
            S = [r for r in R if r['t'] >= 0.5 and (g[0] == 'all' or (r['N'], r['nu']) == g)]
            if not S: continue
            m = np.array([r[f'mmax_{th}'] for r in S])
            out = []
            for key in ('r_med', 'r_max', 'frac_drift_gt_smooth'):
                y = np.array([max(r[f'{key}_{th}'], 1e-12) for r in S]); out.append(pl(m, y) + (np.median(y),))
            sg = np.array([r[f'tp_total_{th}'] for r in S]); bq = np.median([r[f'q_max_{th}'] for r in S])
            print(f"N,nu={g}: n={len(S)} |w|max in [{m.min():.3g},{m.max():.3g}] | "
                  + " | ".join(f"{k}: p={a:+.3f}+-{e:.3f} (median {md:.3g})" for k, (a, e, md) in
                               zip(('median ratio', 'max ratio', 'share drift>smooth'), out))
                  + f" | Bochner max-ratio median {bq:.3g} | two-point dG_visc>0 in {int((sg>0).sum())}/{len(sg)}")
    print("\n== resolution convergence: same (nu, seed) across N, matched t ==")
    keys = sorted({(r['nu'], r['seed']) for r in R})
    for nu, sd in keys:
        byN = {}
        for r in R:
            if r['nu'] == nu and r['seed'] == sd: byN.setdefault(r['N'], {})[r['t']] = r
        if len(byN) < 2: continue
        Ns = sorted(byN); ts = sorted(set.intersection(*[set(round(t, 2) for t in byN[n]) for n in Ns]))
        for tt in ts[::2]:
            row = [min(byN[n].values(), key=lambda r: abs(r['t']-tt)) for n in Ns]
            print(f"nu={nu} seed={sd} t={tt:.2f}: " + "  ".join(
                f"N={r['N']}: |w|max={r['mmax_0.5']:.3g} med={r['r_med_0.5']:.3g} max={r['r_max_0.5']:.3g} share={r['frac_drift_gt_smooth_0.5']:.3f} dG={r['tp_total_0.5']:+.3g}"
                for r in row))

if MODE == 'scale':
    scale_run(float(sys.argv[3]), int(sys.argv[4]), float(sys.argv[5]), float(sys.argv[6]))
elif MODE == 'fit':
    fit(sys.argv[2:])
elif __name__ == '__main__':
    print("NUMERICS, NOT PROOFS. N =", N, "theta = 0.5")
    abc = [np.sin(Z)+np.cos(Y), np.sin(X)+np.cos(Z), np.sin(Y)+np.cos(X)]
    abcp = [abc[i]+0.05*np.sin(2*X+3*Y+Z+i) for i in range(3)]
    shear2 = [np.sin(2*Y)*0+np.sin(Z), np.sin(3*X), 0*X+0.3*np.cos(2*X+Y)]
    for name, u in [("ABC (Beltrami)", abc), ("ABC + perturbation", abcp), ("two-mode shear", shear2)]:
        show(name, diagnostics(project([fft(a) for a in u])))
    for s in range(3):
        show(f"random Fourier k~4 #{s}", diagnostics(random_field()))
    # short Navier-Stokes run: pseudo-spectral, RK4, 2/3 dealiasing
    nu = 0.005; uh = random_field(kpeak=3, amp=1.0)
    def rhs(uh):
        u = [ifft(a) for a in uh]; w = [ifft(a) for a in curl_hat(uh)]
        nl = [u[1]*w[2]-u[2]*w[1], u[2]*w[0]-u[0]*w[2], u[0]*w[1]-u[1]*w[0]]
        nlh = project([fft(a)*dealias for a in nl])
        return [nlh[i]-nu*K2*uh[i] for i in range(3)]
    T, tnow, nextout = 3.0, 0.0, 0.0
    print(f"-- NS evolution, nu={nu}, random datum k~3, unit energy (eddy time ~ 1) --")
    while tnow <= T+1e-9:
        if tnow >= nextout-1e-9:
            show(f"NS t={tnow:.2f}", diagnostics(uh)); nextout += 0.5
        umax = max(np.abs(ifft(a)).max() for a in uh); dt = min(0.4*(L/N)/umax, 0.02)
        k1_ = rhs(uh); k2_ = rhs([uh[i]+dt/2*k1_[i] for i in range(3)])
        k3_ = rhs([uh[i]+dt/2*k2_[i] for i in range(3)]); k4_ = rhs([uh[i]+dt*k3_[i] for i in range(3)])
        uh = [uh[i]+dt/6*(k1_[i]+2*k2_[i]+2*k3_[i]+k4_[i]) for i in range(3)]; tnow += dt
