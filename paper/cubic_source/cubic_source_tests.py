"""Cubic-source grind tests at the vorticity maximum on T^3. NUMERICS, NOT PROOFS.
Author: Benjamin Stanley Frohman. Solver, datum and time stepping copied from ../viscous_balance_tests.py.
At x* = argmax|omega| each snapshot records, with M = |omega(x*)|:
  sigma = omega.S omega (= omega.(omega.grad)u), sigma/M^3, ||S||_inf/M (S = sym grad u, operator norm),
  visc = nu omega.Delta omega / M  (viscous part of M M' / M, should be <= 0),
  logfac = 1 + log^+(||omega||_{H^2}/M)  (log-corrected bound shape), ||S||_inf/(M logfac).
Usage: python cubic_source_tests.py N nu seed T wall out.jsonl
"""
import numpy as np, sys, json, time
N = int(sys.argv[1]); nu = float(sys.argv[2]); seed = int(sys.argv[3]); T = float(sys.argv[4]); wall = float(sys.argv[5])
out = open(sys.argv[6], 'w'); rng = np.random.default_rng(seed)
L = 2*np.pi
k1 = np.fft.fftfreq(N, 1/N); KX, KY, KZ = np.meshgrid(k1, k1, k1, indexing='ij')
K = [KX, KY, KZ]; K2 = KX**2+KY**2+KZ**2; K2s = np.where(K2 == 0, 1, K2)
dealias = (np.abs(KX) < N/3) & (np.abs(KY) < N/3) & (np.abs(KZ) < N/3)
fft, ifft = np.fft.fftn, lambda a: np.real(np.fft.ifftn(a))
def curl_hat(uh): return [1j*(K[1]*uh[2]-K[2]*uh[1]), 1j*(K[2]*uh[0]-K[0]*uh[2]), 1j*(K[0]*uh[1]-K[1]*uh[0])]
def project(uh):
    d = (K[0]*uh[0]+K[1]*uh[1]+K[2]*uh[2])/K2s; return [uh[i]-K[i]*d for i in range(3)]
def random_field(kpeak=3, amp=1.0, M=24):
    km = np.fft.fftfreq(M, 1/M).astype(int); uh = []
    for _ in range(3):
        r = rng.standard_normal((M,)*3)+1j*rng.standard_normal((M,)*3)
        a = np.zeros((N,)*3, complex); a[np.ix_(km % N, km % N, km % N)] = r
        uh.append(a*np.exp(-(np.sqrt(K2)-kpeak)**2/2))
    uh = project([fft(ifft(a)) for a in uh]); uh = [a*dealias for a in uh]
    e = sum((np.abs(a)**2).sum() for a in uh)/N**6; return [a*amp/np.sqrt(e) for a in uh]
def rhs(uh):
    u = [ifft(a) for a in uh]; w = [ifft(a) for a in curl_hat(uh)]
    nl = [u[1]*w[2]-u[2]*w[1], u[2]*w[0]-u[0]*w[2], u[0]*w[1]-u[1]*w[0]]
    nlh = project([fft(a)*dealias for a in nl]); return [nlh[i]-nu*K2*uh[i] for i in range(3)]
def diag(uh, tnow):
    wh = curl_hat(uh); w = np.array([ifft(a) for a in wh]); m = np.sqrt((w**2).sum(0))
    i = np.unravel_index(np.argmax(m), m.shape); M = m[i]
    gu = np.array([[ifft(1j*K[j]*uh[a]) for j in range(3)] for a in range(3)])  # gu[a,j] = d_j u_a
    S = 0.5*(gu+gu.transpose(1, 0, 2, 3, 4)); Sm = np.moveaxis(S, (0, 1), (-2, -1))
    Snorm = np.abs(np.linalg.eigvalsh(Sm)).max()
    wx = w[(slice(None),)+i]; sig = wx @ S[(slice(None), slice(None))+i] @ wx
    lw = np.array([ifft(-K2*a)[i] for a in wh]); visc = nu*(wx @ lw)/M
    h2 = np.sqrt(sum(((1+K2)**2*np.abs(a)**2).sum() for a in wh)/N**6)   # ||w||_{H^2}, normalised mean
    logfac = 1+max(0.0, np.log(h2/M))
    return dict(N=N, nu=nu, seed=seed, t=round(tnow, 4), M=float(M), sigma=float(sig), sig_M3=float(sig/M**3),
                Sinf_M=float(Snorm/M), visc=float(visc), visc_M2=float(visc/M**2), logfac=float(logfac),
                Sinf_Mlog=float(Snorm/(M*logfac)), rate=float(sig/M+visc))
t0 = time.time(); uh = random_field(); tnow, nxt = 0.0, 0.0
while tnow <= T+1e-9 and time.time()-t0 < wall:
    if tnow >= nxt-1e-9:
        out.write(json.dumps(diag(uh, tnow))+'\n'); out.flush(); nxt += 0.05
    umax = max(np.abs(ifft(a)).max() for a in uh); dt = min(0.4*(L/N)/umax, 0.02)
    a1 = rhs(uh); a2 = rhs([uh[k]+dt/2*a1[k] for k in range(3)]); a3 = rhs([uh[k]+dt/2*a2[k] for k in range(3)])
    a4 = rhs([uh[k]+dt*a3[k] for k in range(3)]); uh = [uh[k]+dt/6*(a1[k]+2*a2[k]+2*a3[k]+a4[k]) for k in range(3)]; tnow += dt
