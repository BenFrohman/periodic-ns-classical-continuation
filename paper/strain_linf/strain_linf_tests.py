"""Bahouri-Chemin truncation family on T^3 (z-independent, u3=0).
omega_K = f_K(x) f_K(y) e_z, f_K = (4/pi) sum_{odd k<=K} sin(kx)/k (Dirichlet partial sum of sgn(sin x)).
u = (-d_y psi, d_x psi, 0), Lap psi = omega_K; div u = 0; curl u = omega_K e_z.
Records max|omega| (exact: (max f_K)^2), max_x ||S(x)||_op on a grid (N = 8K), S at origin from
the exact formula S11(0) = (16/pi^2) sum_{odd k,l<=K} 1/(k^2+l^2), and (2/pi) log K.
NUMERICS, NOT PROOFS. Usage: python3 strain_linf_tests.py out.jsonl"""
import numpy as np, json, sys
out = open(sys.argv[1], 'w')
def fmax(K):  # max of 1D partial sum on fine grid near first Gibbs peak + global
    x = np.linspace(1e-6, np.pi/2, 200001); k = np.arange(1, K+1, 2)
    best = 0.
    for c in np.array_split(x, 200):
        best = max(best, (4/np.pi*(np.sin(np.outer(c, k))/k).sum(1)).max())
    return best
for K in [7, 15, 31, 63, 127, 255, 511, 1023]:
    k = np.arange(1, K+1, 2); kk, ll = np.meshgrid(k, k, indexing='ij'); q = kk**2+ll**2
    S0 = 16/np.pi**2*(1/q).sum()
    rec = dict(K=K, S11_origin=S0, two_over_pi_logK=2/np.pi*np.log(K), omega_max=fmax(K)**2)
    if K <= 255:   # full grid sup of ||S||_op via FFT, N = 8K (2D suffices: z-independent)
        N = 8*K; c = np.zeros((N, N)); 
        A = 16/np.pi**2/(kk*ll)           # omega = sum A sin kx sin ly
        # psi = -A/q sin sin ; S11 = -psi_xy = (A kl/q) cos kx cos ly ... evaluate via 2D DCT-like sum
        x = 2*np.pi*np.arange(N)/N
        Ck = np.cos(np.outer(x, k)); Sk = np.sin(np.outer(x, k))
        S11 = Ck @ (A*kk*ll/q) @ Ck.T
        S12 = 0.5*(Sk @ (A*(ll**2-kk**2)/q) @ Sk.T)   # (psi_xx - psi_yy)/2
        W = Sk @ A @ Sk.T
        rec.update(N=N, S_op_sup=float(np.sqrt(S11**2+S12**2).max()), omega_grid_max=float(np.abs(W).max()))
    print(rec, flush=True); out.write(json.dumps(rec)+'\n'); out.flush()
