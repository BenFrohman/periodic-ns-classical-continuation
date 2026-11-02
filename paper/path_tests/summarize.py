import json, glob
for f in sorted(glob.glob('path_tests/N*.jsonl')):
    R = [json.loads(l) for l in open(f)]
    print(f"\n{f}  (seeded at t={R[0]['t']}, max|w| at seed {R[0]['mmax_now']:.3g})")
    for target in (0, 0.1, 0.25, 0.5, 1.0, 1.5, 2.0):
        r = min(R, key=lambda r: abs(r['dt_since_seed']-target))
        print(f" dt={r['dt_since_seed']:.2f} max|w|={r['mmax_now']:.3g} | " + " | ".join(
            f"th={th}: inHigh={r[f'in_high_{th}']:.2f} inBuffer(Lam/2)={r[f'in_buffer_{th}']:.2f} sep med/max={r[f'sep_ratio_med_{th}']:.2f}/{r[f'sep_ratio_max_{th}']:.1f} gap med/p99={r[f'gap_med_{th}']:.3f}/{r[f'gap_p99_{th}']:.3f} Holder p99 Lag/Eul={r[f'holder_lag_p99_{th}']:.3f}/{r[f'holder_eul_p99_{th}']:.3f}"
            for th in (0.5, 0.7)))
