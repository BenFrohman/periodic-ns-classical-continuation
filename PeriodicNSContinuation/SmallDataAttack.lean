/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.IntegrabilityAttack

/-!
# Small data via the enstrophy Riccati inequality (work in progress; names coined)

* `riccati_barrier` — **proved**: if `f' ≤ f (-α + β f²)` (one-sided) and `β f(0)² < α`, `f(0) ≥ 0`,
  then `f ≤ f(0)` on `[0,T']`. This is the ODE half of the classical small-data argument.
* `PeriodicEnstrophyRiccati ν α β` — **hypothesis** (classical, not formalized: enstrophy identity,
  Ladyzhenskaya/Agmon, Young and Poincaré give `E' ≤ -(ν λ/2) E + (C/ν³) E³` for the `H¹`
  quantity `E = ‖u‖²_{H¹}`).
* `PeriodicH1BlowupCriterion ν` — **hypothesis** (classical, Leray 1934: finite `T*` forces
  `‖u‖_{H¹}` to be unbounded).
* `periodicTstar_eq_top_of_smallH1` and `integrability_of_smallH1` — **proved from both**:
  small data `β ‖u₀‖⁴_{H¹} < α` give `T* = ⊤`, and then `∫₀ᵀ‖ω‖_∞ < ∞` for every `T`.

Where it breaks for general data: if `β E(0)² ≥ α`, the cubic term can dominate. The Riccati
inequality `E' ≤ C E³` then allows finite-time blow-up of the comparison ODE, so nothing is
concluded. This is exactly the supercritical gap.
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D

namespace PeriodicNSContinuation

open Corrected

/-- **Proved.** Barrier lemma for `f' ≤ f(-α + β f²)`. -/
theorem riccati_barrier {f f' : ℝ → ℝ} {α β T' : ℝ} (hβ : 0 ≤ β)
    (hf : ContinuousOn f (Icc 0 T'))
    (hd : ∀ x ∈ Ico 0 T', HasDerivWithinAt f (f' x) (Ici x) x)
    (hle : ∀ x ∈ Ico 0 T', f' x ≤ f x * (-α + β * f x ^ 2))
    (h0 : 0 ≤ f 0) (hsmall : β * f 0 ^ 2 < α) :
    ∀ x ∈ Icc 0 T', f x ≤ f 0 := by
  intro x hx
  -- choose ε > 0 with β (f0+ε)² < α, for all small ε
  have key : ∀ ε, 0 < ε → β * (f 0 + ε) ^ 2 < α → f x ≤ f 0 + ε := by
    intro ε hε hεs
    refine image_le_of_deriv_right_lt_deriv_boundary' (B := fun _ => f 0 + ε) (B' := fun _ => 0)
      hf hd (by linarith) continuousOn_const (fun _ _ => hasDerivWithinAt_const _ _ _) ?_ hx
    intro y hy hyB
    have := hle y hy
    rw [hyB] at this
    have hpos : 0 < f 0 + ε := by linarith
    nlinarith [mul_pos hpos (by linarith : (0:ℝ) < α - β * (f 0 + ε) ^ 2)]
  -- continuity of ε ↦ β (f0+ε)²
  by_contra hcon
  replace hcon := not_le.1 hcon
  set δ := f x - f 0 with hδ
  have hδp : 0 < δ := by linarith
  have hcont : Continuous fun ε : ℝ => β * (f 0 + ε) ^ 2 := by fun_prop
  have hev : ∀ᶠ ε in 𝓝 (0:ℝ), β * (f 0 + ε) ^ 2 < α :=
    hcont.continuousAt.eventually_lt continuousAt_const (by simpa using hsmall)
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set ε := min (δ / 2) (η / 2)
  have hε : 0 < ε := lt_min (by linarith) (by linarith)
  have hεη : dist ε 0 < η := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε]; exact (min_le_right _ _).trans_lt (by linarith)
  have := key ε hε (hball hεη)
  have : ε ≤ δ / 2 := min_le_left _ _
  linarith

/-- Coined. `E(v) = ‖v‖²_{H¹}` (Fourier side). -/
def h1Sq (v : VelocityField) : ℝ := hsSq 1 v

/-- Coined. **Hypothesis (classical, not formalized).** Enstrophy Riccati inequality on every
solution interval, with one-sided derivative on `[0,T')`. -/
def PeriodicEnstrophyRiccati (ν α β : ℝ) : Prop :=
  0 < ν → ∀ (u₀ : VelocityField) (u : TimeDependentVelocity) (p : TimeDependentPressure) (T' : ℝ),
    IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T' u p →
    ContinuousOn (fun t => h1Sq (u t)) (Icc 0 T') ∧
    ∀ t ∈ Ico 0 T', ∃ d, HasDerivWithinAt (fun t => h1Sq (u t)) d (Ici t) t ∧
      d ≤ h1Sq (u t) * (-α + β * h1Sq (u t) ^ 2)

/-- Coined. **Hypothesis (classical, Leray 1934, not formalized).** A finite lifespan forces
`‖u‖_{H¹}` to be unbounded. -/
def PeriodicH1BlowupCriterion (ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure), IsPeriodicMaximalSolution ν u₀ u p →
      ∀ T : ℝ, periodicTstar ν u₀ = (T : EReal) →
        ¬ ∃ M : ℝ, ∀ t ∈ Ico (0:ℝ) T, h1Sq (u t) ≤ M

/-- **Proved from the two classical hypotheses.** Small `H¹` data have infinite lifespan. -/
theorem periodicTstar_eq_top_of_smallH1 {ν α β : ℝ} (hν : 0 < ν) (hβ : 0 ≤ β)
    (hR : PeriodicEnstrophyRiccati ν α β) (hL : PeriodicH1BlowupCriterion ν)
    {u₀ : VelocityField} (hu₀ : IsPeriodicSmoothInitialData u₀)
    {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (hm : IsPeriodicMaximalSolution ν u₀ u p) (hsmall : β * h1Sq u₀ ^ 2 < α) :
    periodicTstar ν u₀ = ⊤ := by
  rcases tstar_eq_top_or_coe hν hu₀ with h | ⟨T, hT⟩
  · exact h
  · exfalso
    apply hL hν u₀ hu₀ u p hm T hT
    refine ⟨h1Sq u₀, fun t ht => ?_⟩
    obtain ⟨hsol, htm, -⟩ := sol_around hm hT ht
    obtain ⟨hc, hd⟩ := hR hν u₀ u p _ hsol
    have hu0 : u 0 = u₀ := u_zero hsol
    choose! d hdd hdle using hd
    have := riccati_barrier hβ hc hdd hdle (by rw [hu0]; exact hsSq_nonneg 1 u₀)
      (by simpa [hu0] using hsmall) t htm
    simpa [hu0] using this

/-- **Proved from the two classical hypotheses.** Small-data `PeriodicBKMIntegrability`. -/
theorem integrability_of_smallH1 {ν α β : ℝ} (hν : 0 < ν) (hβ : 0 ≤ β)
    (hR : PeriodicEnstrophyRiccati ν α β) (hL : PeriodicH1BlowupCriterion ν)
    {u₀ : VelocityField} (hu₀ : IsPeriodicSmoothInitialData u₀)
    {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (hm : IsPeriodicMaximalSolution ν u₀ u p) (hsmall : β * h1Sq u₀ ^ 2 < α) (T : ℝ) :
    IntegrableOn (fun t => vorticity_sup_norm (vorticity (u t))) (Icc 0 T) :=
  integrableOn_vorticity_of_lt_tstar hν hm
    (by rw [periodicTstar_eq_top_of_smallH1 hν hβ hR hL hu₀ hm hsmall]; exact EReal.coe_lt_top T)

end PeriodicNSContinuation
