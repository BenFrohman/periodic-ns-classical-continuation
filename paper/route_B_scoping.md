# Scoping dynamic routes to Frohmanian Tether Hypothesis (B) without BKM

Status: **no non-circular route found.** This note is on paper only; nothing in it is a theorem
unless it is cited as a Lean declaration.

## Setup
Along trajectories, $D\tau/Dt = (I-\tau\otimes\tau)S\tau + \nu(I-\tau\otimes\tau)\Delta\omega/|\omega|$
(see `DirectionEvolution.lean`). The input is `FrohmanianDirectionCoercivity`: bending is $o(|\omega|)$ on the high set.

## Routes, and where each one fails
1. **Lagrangian two-point integration** (`twoPoint_direction_drift`, proved). Fails at
   $\int_0^{T^*}\|\omega\|_\infty\,dt<\infty$ (BKM), at the viscous term, and at trajectory separation, which needs $\int\|\nabla u\|_\infty$.
2. **Gradient transport for $\nabla\tau$.** $D(\nabla\tau)/Dt$ contains $\nabla(\text{bend})$, and that involves
   $\nabla S\sim\nabla\omega$. Pointwise control of bending says nothing about its gradient. Fails at needing
   $\|\nabla\omega\|_\infty$, which is stronger than BKM.
3. **Nonlocal Constantin–Fefferman kernel** (`ConstantinKernel.lean`). Bending is a PV integral whose geometric
   kernel vanishes when $\tau(x+y)\parallel\tau(x)$, **including antiparallel**. So bending control is blind
   to sign flips (`PlanarObstruction.lean`: zero bending, Hölder constant $\ge2\sqrt{n/\pi}$). Even modulo sign,
   inverting an $|\omega|/|y|^3$-weighted average of $|\sin\angle|$ into a pointwise two-point bound needs a
   lower bound on $|\omega|$ near $x$ (thickness of the high set). That is not available, so this route fails there.
4. **Parabolic, geometric-depletion style** (Grujić-type sparseness, Giga–Miura). These need an a priori
   sparseness or scale hypothesis on the super-level sets, which is a new assumption of the same strength.
   Not pursued.

## Honest consequence and a non-drift suggestion
The Constantin–Fefferman and Beirão da Veiga–Berselli criteria use $|\sin\angle(\omega(x),\omega(y))|$, which is
regularity of the vorticity **line field**, not of the signed direction $\tau$. Part (B) as currently
stated, ½-Hölder $\tau$, is stronger than those criteria need, and the planar obstruction refutes any
pointwise route to it. A line-field version of (B) would be weaker and still sufficient. It is **suggested,
not added**, pending your approval.

## Update: line version (B_line), attack on (A) ⇒ B_line
Signed and line versions are both kept. Along two trajectories, with (A) (bending $\le C$), the bending part of the drift is
$\le 2CT^*$, which is finite, so failure (i) disappears for (A); it remains for `FrohmanianDirectionCoercivity`.
The remaining failing steps for (A) ⇒ B_line are:
(ii) the viscous term $\nu(I-\tau\otimes\tau)\Delta\omega/|\omega|$, which no hypothesis bounds;
(iii) the conversion from Lagrangian to Eulerian distance, $|X(x,t)-X(y,t)|\gtrsim|x-y|^{?}$, which needs a Lipschitz or Hölder flow map, that is $\int\|\nabla u\|_\infty$ (BKM-strength);
(iv) trajectories that leave the high set, where (A) gives no bending bound.

## Step (ii): the viscous term (`ViscousDirection.lean`, Nov 2026)

Proved in Lean, with 0 sorry: $\nu(I-\tau\otimes\tau)\Delta\omega/|\omega| = \nu\big[(I-\tau\otimes\tau)\Delta\tau + 2(\nabla\log|\omega|\cdot\nabla)\tau\big]$ (algebraic form). The projection kills $\tau\Delta|\omega|$. For a unit field, $\langle\tau,\partial_v\tau\rangle=0$. If $\langle\tau,L\rangle=-g$, then $(I-\tau\otimes\tau)L=L+g\tau$, which gives the harmonic-map form $\Delta\tau+|\nabla\tau|^2\tau$.

The exact gap is still open:
1. **No good-sign maximum principle.** Bochner gives $(\partial_t-\Delta)|\nabla\tau|^2\le-2|\nabla^2\tau|^2+C|\nabla\tau|^4$. The target $S^2$/$\mathbb{RP}^2$ has positive curvature, so the quartic term has the bad sign, and harmonic-map heat flow into spheres can blow up in finite time. A two-point maximum principle on the line gap gives dissipation only at an interior maximum, and only modulo the drift.
2. **Drift.** $2\nu(\nabla\log|\omega|\cdot\nabla)\tau$ needs $\sup_{\text{high set}}|\nabla\log|\omega||$. That quantity is not controlled by (A), and a bound on it is not weaker than the regularity it would serve. So it is deliberately **not** named as a Prop (no-drift rule).
3. **Coupling.** The $\tau$ equation is not closed: $|\omega|$, the bending terms and the drift all feed back through Biot–Savart.

Conclusion: the viscous term is not an obstruction in sign at points where $|\nabla\tau|$ is small, but no estimate with constants bounded by (A) is known. Step (ii) stays open.

## Gaps (iv) exit from the high set and (iii) Lagrangian-to-Eulerian transfer (`HighSetExit.lean`, Nov 2026)

**Exit along a path.** Write $m(t)=|\omega(X(t),t)|$. Then $\dot m=\alpha m+\nu\,\Delta\omega\cdot\tau$, where $\alpha=\tau\cdot S\tau$.

Proved in Lean (`lower_gronwall_exp`, `buffer_stay_time`): if $\dot m\ge -a m$, then $m(t)\ge m(0)e^{-at}$. So a path starting in $\{m\ge 2\Lambda\}$ stays in $\{m\ge\Lambda\}$ for $t\le \log 2/a$.

The required rate is $a\ge \sup(-\alpha)+\nu\sup|\Delta\omega\cdot\tau|/|\omega|$ on $\{m\ge\Lambda\}$.
- Hypothesis (A) controls only the orthogonal strain $(I-\tau\otimes\tau)S\tau$. It does not control the longitudinal rate $\alpha$, and it does not control $\nu|\Delta\omega|/|\omega|$.
- $|\alpha|\le|S|$ is a $\|\nabla u\|_\infty$ quantity, so it is at BKM level.
- The buffer helps only if $a\cdot T_*\lesssim 1$ over the window $T_*$ that the direction argument needs. Under scaling, $a\sim\|\omega\|_\infty$ and $T_*\sim\|\omega\|_\infty^{-1}$, which is borderline. Closing it needs an absolute constant.
- No Prop is named, per the no-drift rule.

**Lagrangian versus Eulerian.** Only the following was checked against sources this turn:
- Constantin–Fefferman (1993) is Eulerian, at fixed time. Its condition is $|\sin\theta(x,y,t)|\le C|y|$ on the high set.
- Chae (Rev. Mat. Iberoam., EMS Press) is also Eulerian. It uses Triebel–Lizorkin regularity of $\xi=\omega/|\omega|$ together with integrability of $|\omega|$.
- Deng–Hou–Yu (CPDE 2005/2006) is for **Euler**. It is "Lagrangian" in the sense of following a vortex-line segment near the maximum (its length, its curvature $\kappa$, $\nabla\cdot\xi$, and the tangential and normal velocities). It is not a statement about direction regularity along particle trajectories.

I found no verified criterion stated purely in particle-trajectory coordinates. Any such statement would have to return to Eulerian separation through $|X_a-X_b|(t)\le|a-b|\exp\int\|\nabla u\|_\infty$, which is the BKM integral. Gap (iii) is therefore open, and the cost of the transfer is exactly that factor.

**Numerics** (`paper/path_tests/`, numerics only, not proofs):
- **Exit from the high set.** Tracers seeded at the enstrophy peak leave the fixed set $\{|\omega|\ge\theta\max\}$ quickly: 40–80% are gone within 0.1 time units, and almost all by 1.0.
- **The half-threshold buffer.** It keeps 91–100% of tracers up to 0.25 time units, 72–96% at 0.5, and 10–94% at 1.0. Retention is worse at lower $\nu$.
- **Pair separation.** One-cell pairs separate by a median factor of 2–4 and a maximum of 18–35 over 2 time units.
- **Hölder quotient.** The 99th-percentile Hölder-1/2 quotient measured with the initial (Lagrangian) separation is larger than the one measured with the current (Eulerian) separation, about 3.2 against 2–2.9. Pair stretching therefore makes the Eulerian quotient look better. The one-cell gaps reach $p_{99}\approx1$ at low $\nu$, so the direction field is under-resolved at grid scale there.

## The scale-critical product $a\,T_*$ (`ScaleCriticalBuffer.lean`, Nov 2026)

**Proved in Lean.**
- Under NS scaling, the rate-to-threshold ratio $a/\Lambda$ is invariant (`rescalePath_rate`).
- With $a\le c\Lambda$, the stay time is at least $\log 2/(c\Lambda)$ (`buffer_stay_time_ratio`).
- $\langle\tau,\Delta\omega\rangle=\Delta|\omega|-|\omega||\nabla\tau|^2$ (`inner_viscous_along`). At a spatial maximum, therefore, the viscous term only pushes $|\omega|$ down.

**Derivation.** What is needed is an absolute $c$ with
$$\sup_{|\omega|\ge\theta\|\omega\|_\infty}\Big(-\alpha-\nu\,\tfrac{\Delta\omega\cdot\tau}{|\omega|}\Big)\le c\,\|\omega\|_\infty.$$
Known results give only $\|S\|_\infty\lesssim\|\omega\|_\infty(1+\log^+\ldots)$ (Beale–Kato–Majda). There is no pointwise bound $|S|\le C|\omega|$. Even with an absolute $c$, the window lasts $\sim 1/\|\omega\|_\infty$. Chaining windows with the (A)-controlled drift (rate $2B$) costs $\sum_k 1\sim\int\|\omega\|_\infty\,dt$, which is the BKM integral. An absolute $c$ makes each window scale-critical, but it does not close (B). It is left unnamed (no drift).

**Numerics** (`paper/rate_tests/`; 320 snapshots, 64³/96³, $\nu\in\{0.01,0.005,0.0025\}$; numerics, not proofs). Here $aT_*:=a/\|\omega\|_\infty$.
- **$\theta=0.5$.** $aT_*\le 0.29$, median $0.145$. The fit in $\|\omega\|_\infty$ gives $p=-0.07\pm0.04$, which is flat (scale-critical, as predicted). The implied stay time is at least $2.4/\|\omega\|_\infty$.
- **$\theta=0.7$.** $aT_*\le 0.25$, median $0.095$, with $p=+0.03\pm0.09$.
- **$\theta=0.9$.** $aT_*\le 0.20$. The power-law fits there are meaningless, because $a$ is often about $0$.
- **Strain.** $\|S\|_\infty/\|\omega\|_\infty\le 0.76$ throughout.
- **Which term sets $a$.** Compression ($-\alpha$) dominates at low $\nu$ and the viscous term at high $\nu$.
- **Caveat.** The range of $\|\omega\|_\infty$ is narrow (7–50) and the data come from a single family of initial conditions. This is no evidence of an absolute constant under blow-up scaling.

## Window drift cancellation (Nov 2 2026, `WindowCancellation.lean`)
Proved (abstract, Hilbert space): $\|\sum_{k<n}d_k\|\le nB$; $\|\sum d_k\|^2=\sum_{j,k}\langle d_j,d_k\rangle$;
`WindowCorrelationSum` $C$ $\Rightarrow\|\sum d_k\|\le\sqrt{Cn}$; orthogonal increments $\Rightarrow\le B\sqrt n$.
Structural point: $\sum d_k=\delta\tau_n-\delta\tau_0$ telescopes, so $|\cdot|\le2$ trivially. The real target is
$|\delta\tau|/|x-y|^{1/2}$ uniform in $n$; $\sqrt n\sim(\int\|\omega\|_\infty)^{1/2}$ would still be unbounded.
Numerics (`paper/window_tests/`): cumulative drift $\sim n^{0.46\text{–}0.64}$ (random-walk-like, not linear);
$\mathrm{cum}/L^1\approx0.13$–$0.34$, $\mathrm{cum}/L^2\approx0.9$–$1.8$; lag-1 increment correlation is **positive** ($\approx+0.5$),
so cancellation comes from longer lags. Hölder quotient at window end is $\approx0.65$–$1.13$, with no clear trend in $\|\omega\|_{\max}$ (20–48).
Caveats: saturation at the ceiling 2, pairs leave the high set, small N, short time. Open: any bound on the correlation sum for NS.

## Small-separation gain (Nov 2 2026, `SmallSeparationGain.lean`)
Derivation: by Taylor expansion, one window of length $\sim1/\|\omega\|_\infty$ changes $\delta\tau$ by roughly $r\,\sup_{\text{window}}|\nabla\tau|$,
so the per-window constant $L$ is a direction-gradient bound. That is the quantity part (A)/FDC must control (Constantin–Fefferman
needs $|\sin\theta|\le C|y|$ in the high set). Proved: `drift_le_lip_sum` ($\|\delta_n-\delta_0\|\le L\sum_{k<n}r_k$) and
`holder_quotient_of_dominated`: with `SeparationSumDominated r A` ($\sum_{k<n}r_k\le A r_n$, e.g. geometric separation growth),
$\|\delta_n\|\le(K_0+LA\sqrt R)\sqrt{r_n}$, uniform in $n$. This is a reduction to (A), not a proof of (A).
Numerics (`paper/offset_tests/`, offsets 1/2/4/8 cells): per-window line drift $\sim r^\gamma$ with $\gamma\approx0.28$–$0.70$ overall and
$0.26$–$0.40$ in the high set. $\gamma$ falls as $\nu$ falls / $\|\omega\|_{\max}$ rises, below the needed $1/2$ at the most turbulent runs.
The median Hölder quotient at offset 1 grows from 0.64 ($\|\omega\|_{\max}=20$) to 1.09–1.32 ($40$–$48$). Verdict: no evidence yet of a
uniform small-separation gain. The trend is unfavourable, with grid-scale caveats.

## JHTDB comparison (Nov 2 2026)
See `paper/jhtdb_tests/summary.txt` (isotropic1024coarse, public testing token). Numerics only: $\beta\approx0.55$–$0.65$, high-set $\gamma\approx0.58$ at 2–17 Kolmogorov lengths (near-dissipative scales, so Taylor-like $\gamma$ is expected), one run. No proof claim.
