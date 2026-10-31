/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.TetherClaimAttack
import PeriodicNSContinuation.EnstrophyIdentity

/-!
# Toward the direction-of-vorticity criterion on `T³`

Work in progress. **Nothing here proves `PeriodicBKMIntegrability` or Clay (B).**

Classical sources (credited, not re-derived here):
* P. Constantin and C. Fefferman, *Direction of vorticity and the problem of global regularity
  for the Navier–Stokes equations*, Indiana Univ. Math. J. 42 (1993) 775–789 (Lipschitz direction;
  geometric depletion of the Biot–Savart strain kernel).
* H. Beirão da Veiga and L. C. Berselli, *On the regularizing effect of the vorticity direction in
  incompressible viscous flows*, Differential Integral Equations 15 (2002) 345–356 (½-Hölder).

## Decomposition of `PeriodicDirectionCriterion` (`VortDirHolderHalf` ⇒ no finite lifespan)
1. `periodicEnstrophyIdentity` — **proved earlier, unconditional**: `E = ‖u‖²_{H¹}` is
   differentiable on `(0,T')` with derivative `rateOf 1 …`.
2. `PeriodicDirectionEnstrophyGrowth ν` — **OPEN here (classical, not formalized)**: under
   `VortDirHolderHalf` on `[0,T*)` the rate is at most `A · E` for one constant `A`. This packages
   the Constantin–Fefferman geometric depletion of the strain kernel (the kernel factor vanishes
   when `ξ(x) = ξ(y)`, so it is `≤ K|x−y|^{1/2}`) plus the Beirão da Veiga–Berselli interpolation.
   The classical argument gives a bound `g(t)·E` with `g ∈ L¹(0,T*)` (via the energy inequality);
   the constant-`A` form used here is a coined simplification, also unproved.
3. `exp_gronwall_Ioo` — **proved**: linear Grönwall from derivatives on `Ioo`.
4. `PeriodicH1BlowupCriterion ν` — **OPEN here (classical, Leray 1934)**, from `SmallDataAttack`.
* `periodicDirectionCriterion_of_growth` — **proved**: 1 + 2 + 3 + 4 ⇒ `PeriodicDirectionCriterion`.
* `periodicBKMIntegrability_of_directionGrowth` — **proved (conditional)**: additionally assumes
  the OPEN `PeriodicDirectionRegularity ν` (no tether term). That last Prop is the Clay core.
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D

namespace PeriodicNSContinuation

open Corrected

/-- **Proved.** Linear Grönwall with two-sided derivatives on `Ioo 0 T'`:
`f' ≤ A f` gives `f x ≤ f 0 · exp (A x)` on `[0,T']`. -/
theorem exp_gronwall_Ioo {f f' : ℝ → ℝ} {A T' : ℝ} (hf : ContinuousOn f (Icc 0 T'))
    (hd : ∀ x ∈ Ioo 0 T', HasDerivAt f (f' x) x) (hle : ∀ x ∈ Ioo 0 T', f' x ≤ A * f x) :
    ∀ x ∈ Icc 0 T', f x ≤ f 0 * Real.exp (A * x) := by
  set g : ℝ → ℝ := fun x => Real.exp (-(A * x)) * f x with hg
  have hgc : ContinuousOn g (Icc 0 T') :=
    ((Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)).continuousOn).mul hf
  have hgd : ∀ x ∈ Ioo 0 T', HasDerivAt g
      (Real.exp (-(A * x)) * (-A) * f x + Real.exp (-(A * x)) * f' x) x := by
    intro x hx
    have h1 : HasDerivAt (fun x => Real.exp (-(A * x))) (Real.exp (-(A * x)) * (-A)) x := by
      have := ((hasDerivAt_id x).const_mul A).neg.exp
      simpa using this
    exact h1.mul (hd x hx)
  have hanti : AntitoneOn g (Icc 0 T') := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T') hgc
    · intro x hx
      rw [interior_Icc] at hx
      exact (hgd x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hgd x hx).deriv]
      have he := Real.exp_pos (-(A * x))
      have := hle x hx
      nlinarith
  intro x hx
  have h0 : (0:ℝ) ∈ Icc 0 T' := ⟨le_rfl, hx.1.trans hx.2⟩
  have := hanti h0 hx hx.1
  simp only [hg, mul_zero, neg_zero, Real.exp_zero, one_mul] at this
  have hmul := mul_le_mul_of_nonneg_left this (Real.exp_pos (A * x)).le
  rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at hmul
  linarith [mul_comm (f 0) (Real.exp (A * x))]

/-- Coined. **Hypothesis (OPEN here; classical content: Constantin–Fefferman 1993 geometric
depletion + Beirão da Veiga–Berselli 2002; not formalized).** On a maximal solution with
`½`-Hölder vorticity direction up to a finite lifespan `T`, the enstrophy rate is at most `A · E`
for one constant `A`. Constant-`A` form is a coined simplification of the classical `g ∈ L¹`. -/
def PeriodicDirectionEnstrophyGrowth (ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure), IsPeriodicMaximalSolution ν u₀ u p →
      ∀ T : ℝ, periodicTstar ν u₀ = (T : EReal) → VortDirHolderHalf u T →
        ∃ A : ℝ, ∀ t ∈ Ioo (0:ℝ) T,
          rateOf 1 (fourierNSField ν (fourierCoeffVF (u t))) (fourierCoeffVF (u t)) ≤
            A * h1Sq (u t)

/-- **Proved** from the unconditional enstrophy identity, `PeriodicDirectionEnstrophyGrowth` and
`PeriodicH1BlowupCriterion`: the direction criterion `PeriodicDirectionCriterion`. -/
theorem periodicDirectionCriterion_of_growth {ν : ℝ} (hG : PeriodicDirectionEnstrophyGrowth ν)
    (hL : PeriodicH1BlowupCriterion ν) : PeriodicDirectionCriterion ν := by
  intro hν u₀ hu₀ u p hm T hT hdir
  obtain ⟨A, hA⟩ := hG hν u₀ hu₀ u p hm T hT hdir
  apply hL hν u₀ hu₀ u p hm T hT
  refine ⟨h1Sq u₀ * Real.exp (max A 0 * T), fun t ht => ?_⟩
  obtain ⟨hsol, htm, hle⟩ := sol_around hm hT ht
  obtain ⟨hc, hd⟩ := periodicEnstrophyIdentity ν hν u₀ u p _ hsol
  have hu0 : u 0 = u₀ := u_zero hsol
  have key := exp_gronwall_Ioo (f := fun t => h1Sq (u t)) (A := max A 0) hc
    (fun x hx => (hd x hx).2) (fun x hx => by
      have h1 := hA x ⟨hx.1, lt_of_lt_of_le hx.2 hle⟩
      have := mul_le_mul_of_nonneg_right (le_max_left A 0) (hsSq_nonneg 1 (u x))
      exact h1.trans this) t htm
  simp only [hu0] at key
  refine key.trans (mul_le_mul_of_nonneg_left ?_ (hsSq_nonneg 1 u₀))
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2.le (le_max_right A 0))

/-- **Proved (conditional).** `PeriodicBKMIntegrability` from the two classical hypotheses and the
OPEN `PeriodicDirectionRegularity` (direction control for plain NS, the Clay core). -/
theorem periodicBKMIntegrability_of_directionGrowth {ν : ℝ}
    (hG : PeriodicDirectionEnstrophyGrowth ν) (hL : PeriodicH1BlowupCriterion ν)
    (hR : PeriodicDirectionRegularity ν) : PeriodicBKMIntegrability ν :=
  periodicBKMIntegrability_of_direction (periodicDirectionCriterion_of_growth hG hL) hR

end PeriodicNSContinuation
