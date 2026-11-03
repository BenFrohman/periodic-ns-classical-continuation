"""Window-drift / small-separation / Holder-quotient tests on JHTDB isotropic1024coarse.
Access: givernylocal with the public pyJHTDB testing token (<= 4096 points per query).
usage: python jhtdb_windows.py t0 nwin out.npz
Window length = 1/omega_ref with omega_ref = max |omega| over 20*4096 random samples at t0 (a lower bound
for ||omega||_inf). High set = |omega| >= 0.5*omega_ref. Pairs: high-set seed + offset of 1/2/4/8 grid cells
(dx = 2pi/1024; also 16/32 cells) along a random axis; tracked by JHTDB particle tracking (pchip, lag6)."""
import sys, os, time, numpy as np
from givernylocal.turbulence_dataset import turb_dataset
from givernylocal.turbulence_toolkit import getData
t0, nwin, out = float(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
c0 = turb_dataset(dataset_title='isotropic1024coarse', output_path='/workspace/archive/jhtdb', auth_token='x')
tok = c0.metadata['constants']['pyJHTDB_testing_token']
cube = turb_dataset(dataset_title='isotropic1024coarse', output_path='/workspace/archive/jhtdb', auth_token=tok)
L, dx, nu = 2*np.pi, 2*np.pi/1024, 0.000185
rng = np.random.default_rng(int(t0*1000))
def retry(f, *a, **k):
    for i in range(12):
        try: return f(*a, **k)
        except Exception as e:
            print('retry', i, repr(e)[:120], flush=True); time.sleep(min(300, 10*2**i))
    raise RuntimeError('JHTDB unreachable after retries')
def grad(P, t): return np.asarray(retry(getData, cube, 'velocity', float(t), 'none', 'fd4lag4', 'gradient', P % L, verbose=False)[0], dtype=float)
def vort(g): return np.stack([g[:, 7]-g[:, 5], g[:, 2]-g[:, 6], g[:, 3]-g[:, 1]], 1)
ck = out + '.ckpt.npz'
NSAMP = int(os.environ.get('NSAMP', '100'))
if os.path.exists(out + '.seed.npz'):
    zz = np.load(out + '.seed.npz'); cand, cw = zz['cand'], zz['cw']
else:
    cand, cw = [], []
    for i in range(NSAMP):
        P = rng.uniform(0, L, (4096, 3)); w = np.linalg.norm(vort(grad(P, t0)), axis=1)
        cand.append(P); cw.append(w)
    cand, cw = np.vstack(cand), np.concatenate(cw)
    for it in range(3):  # local search: 16 jittered neighbours (within 3 dx) of each of the top 256 points
        top = cand[np.argsort(cw)[-256:]]
        P = np.repeat(top, 16, 0) + rng.uniform(-3, 3, (4096, 3))*dx
        w = np.linalg.norm(vort(grad(P, t0)), axis=1); cand = np.vstack([cand, P]); cw = np.concatenate([cw, w])
    np.savez_compressed(out + '.seed.npz', cand=cand, cw=cw)
wref = cw.max(); thr = 0.5*wref
hs = cand[cw >= thr]; print('omega_ref', wref, 'rms', np.sqrt((cw**2).mean()), 'high-set seeds', len(hs), flush=True)
if len(hs) < 64:  # too few: take the top 64 samples instead (recorded)
    hs = cand[np.argsort(cw)[-64:]]; thr = cw[np.argsort(cw)[-64]]
OFFS = np.array([1, 2, 4, 8, 16, 32]); npair = 2046; off = OFFS[np.arange(npair) % len(OFFS)]
A = hs[rng.integers(0, len(hs), npair)]; B = A + np.eye(3)[rng.integers(0, 3, npair)]*(off*dx)[:, None]
dtw = 1.0/wref; D, SEP, INHI, T, WA, WB = [], [], [], [], [], []
t = t0; k0 = 0
if os.path.exists(ck):
    zc = np.load(ck); A, B, t, k0 = zc['A'], zc['B'], float(zc['t']), int(zc['k'])
    D, SEP, INHI, T, WA, WB = [list(zc[x]) for x in ('D', 'SEP', 'INHI', 'T', 'WA', 'WB')]; print('resume at', k0, flush=True)
for k in range(k0, nwin+1):
    w = vort(grad(np.vstack([A, B]), t)); wa, wb = w[:npair], w[npair:]
    ma, mb = np.linalg.norm(wa, axis=1), np.linalg.norm(wb, axis=1)
    ta, tb = wa/ma[:, None], wb/mb[:, None]
    if k > 0:  # keep tau continuous along each path (sign of omega/|omega| is physical; this is a no-op unless sampling flips)
        pass
    D.append(ta-tb); SEP.append(np.linalg.norm((B-A+L/2) % L-L/2, axis=1)); INHI.append((ma >= thr) & (mb >= thr))
    T.append(t); WA.append(ma); WB.append(mb)
    if k == nwin: break
    t1 = t + dtw
    P = np.asarray(retry(getData, cube, 'position', float(t), 'pchip', 'lag6', 'field', np.vstack([A, B]) % L,
                           option=[float(t1), 0.0005], verbose=False)[0], dtype=float)
    # unwrap so separations are measured continuously
    A = A + ((P[:npair] - A + L/2) % L - L/2); B = B + ((P[npair:] - B + L/2) % L - L/2); t = t1
    if k % 5 == 4:
        np.savez_compressed(ck + '.tmp.npz', A=A, B=B, t=t, k=k+1, D=np.array(D), SEP=np.array(SEP), INHI=np.array(INHI), T=np.array(T), WA=np.array(WA), WB=np.array(WB))
        os.replace(ck + '.tmp.npz', ck)
    if k % 10 == 0: print('window', k, 't', round(t, 4), 'inhigh', np.mean(INHI[-1]), flush=True)
np.savez_compressed(out, D=np.array(D), SEP=np.array(SEP), INHI=np.array(INHI), T=np.array(T), M=np.full(len(T), wref),
                    WA=np.array(WA), WB=np.array(WB), off=off, N=1024, nu=nu, thr=thr)
