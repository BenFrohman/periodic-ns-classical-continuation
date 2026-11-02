import json, glob, numpy as np
R = [json.loads(l) for f in sorted(glob.glob('rate_tests/N*.jsonl')) for l in open(f) if l.startswith('{')]
print(f"{len(R)} snapshots. NUMERICS, NOT PROOFS. a*T_* := a/max|w|, a = max over high set of -(m'/m)")
for th in (0.5, 0.7, 0.9):
    print(f"\n== theta={th} ==")
    for g in sorted({(r['N'], r['nu']) for r in R}):
        S = [r for r in R if (r['N'], r['nu']) == g and r['t'] >= 0.3]
        a = np.array([r[f'a_{th}'] for r in S]); m = np.array([r['mmax'] for r in S])
        p, cov = np.polyfit(np.log(m), np.log(np.maximum(a, 1e-6)), 1, cov=True)
        print(f"N,nu={g}: n={len(S)} max|w| [{m.min():.3g},{m.max():.3g}] aT*: max={a.max():.3f} med={np.median(a):.3f} "
              f"p99-pt med={np.median([r[f'a_p99_{th}'] for r in S]):.3f} | -alpha/max|w| max={max(r[f'negalpha_{th}'] for r in S):.3f} "
              f"visc/max|w| max={max(r[f'visc_{th}'] for r in S):.3f} | |S|/max|w| on set max={max(r[f'Smax_{th}'] for r in S):.3f} "
              f"| fit aT* ~ max|w|^p: p={p[0]:+.3f}+-{np.sqrt(cov[0,0]):.3f}")
    a = np.array([r[f'a_{th}'] for r in R if r['t'] >= 0.3]); m = np.array([r['mmax'] for r in R if r['t'] >= 0.3])
    p, cov = np.polyfit(np.log(m), np.log(np.maximum(a, 1e-6)), 1, cov=True)
    print(f"ALL: aT* max={a.max():.3f} med={np.median(a):.3f}; fit p={p[0]:+.3f}+-{np.sqrt(cov[0,0]):.3f}; implied stay log2/a in units of 1/max|w|: min={np.log(2)/a.max():.2f}")
print("\n||S||_inf/||w||_inf: max", max(r['Sinf_over_winf'] for r in R), "median", np.median([r['Sinf_over_winf'] for r in R]))
