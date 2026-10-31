/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.FourierInversion
import TorusFourierNS.TameTransport

/-!
# Propagation of higher regularity via the tame Galerkin estimate

**Proved:** `fourierHigherRegularity_of (0 ≤ ν) (5/2 < s)`:
`FourierGalerkinApproximation ν s → FourierHigherRegularity ν s`.
The proof uses the tame Galerkin bound `galerkin_hs_propagation` (torus-fourier-ns-lemmas) for
every `r = max s' 2`, then `hsNormField_extendG_restrictG_le`, and passes to the limit with Fatou
(`hs_of_tendsto`).

**NOT proved** (coined): `FourierGalerkinApproximation ν s`. It says the given `H^s` Fourier solution
is a mode-wise limit on `[0,T]` of Galerkin solutions from the truncated data, with a uniform
`H^s` bound. This is a stability/uniqueness statement for the Fourier system and is the
remaining gap for `FourierHigherRegularity`.
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D

namespace PeriodicNSContinuation

/-- **NOT proved** (coined). The Fourier solution is a limit of uniformly `H^s` Galerkin solutions. -/
def FourierGalerkinApproximation (ν s : ℝ) : Prop :=
  ∀ u₀ : NavierStokes3D.VelocityField, IsPeriodicSmoothInitialData u₀ → ∀ T : ℝ, 0 < T →
    ∀ (M : ℝ) (a : ℝ → TorusFourierNS.FField), IsFourierSolutionOn ν s M u₀ T a →
      ∃ (N : ℕ → ℕ) (α : ∀ n, ℝ → TorusFourierNS.GState (N n)) (A : ℝ),
        (∀ n, α n 0 = TorusFourierNS.restrictG (N n) (fourierCoeffVF u₀)) ∧
        (∀ n, ∀ t ∈ Icc 0 T,
          HasDerivAt (α n) (TorusFourierNS.galerkinNSField (N n) ν (α n t)) t) ∧
        (∀ n, ∀ t ∈ Icc 0 T, TorusFourierNS.HermitianField (TorusFourierNS.extendG (α n t)) ∧
          TorusFourierNS.DivergenceFree (TorusFourierNS.extendG (α n t))) ∧
        (∀ n, ∀ t ∈ Icc 0 T, TorusFourierNS.hsNormField s (TorusFourierNS.extendG (α n t)) ≤ A) ∧
        (∀ t ∈ Icc 0 T, ∀ k i,
          Tendsto (fun n => TorusFourierNS.extendG (α n t) k i) atTop (𝓝 (a t k i)))

/-- **Proved.** Galerkin `H^s` norms are monotone in `s`. -/
lemma hsNormField_extendG_mono {s r : ℝ} (hsr : s ≤ r) {N : ℕ} (v : TorusFourierNS.GState N) :
    TorusFourierNS.hsNormField s (TorusFourierNS.extendG v) ≤
      TorusFourierNS.hsNormField r (TorusFourierNS.extendG v) := by
  have h2 : TorusFourierNS.hsNormField s (TorusFourierNS.extendG v) ^ 2 ≤
      TorusFourierNS.hsNormField r (TorusFourierNS.extendG v) ^ 2 := by
    rw [TorusFourierNS.hsNormSq_extendG, TorusFourierNS.hsNormSq_extendG]
    refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun i _ => ?_
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [TorusFourierNS.sobW_eq, TorusFourierNS.sobW_eq]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [TorusFourierNS.nsq_nonneg k.1]) hsr
  exact (pow_le_pow_iff_left₀ (TorusFourierNS.hsNormField_nonneg _ _)
    (TorusFourierNS.hsNormField_nonneg _ _) two_ne_zero).1 h2

/-- **Proved (`ν ≥ 0`, `5/2 < s`).** -/
theorem fourierHigherRegularity_of {ν s : ℝ} (hν : 0 ≤ ν) (hs : 5 / 2 < s)
    (hG : FourierGalerkinApproximation ν s) : FourierHigherRegularity ν s := by
  intro u₀ hu₀ T hT M a ha s'
  obtain ⟨N, α, A, h0, hder, hstr, hA, hlim⟩ := hG u₀ hu₀ T hT M a ha
  set r := max s' 2
  have hr2 : 2 ≤ r := le_max_right _ _
  set C := TorusFourierNS.tameConst s r
  have hC : 0 ≤ C := TorusFourierNS.tameConst_nonneg hr2
  have hA0 : 0 ≤ A := (TorusFourierNS.hsNormField_nonneg _ _).trans (hA 0 0 ⟨le_rfl, hT.le⟩)
  set H := TorusFourierNS.hsNormField r (fourierCoeffVF u₀)
  set R := Real.sqrt (H ^ 2 * Real.exp (C * A * T))
  refine ⟨R, fun t ht => ?_⟩
  have hbd : ∀ n, TorusFourierNS.hsNormField s' (TorusFourierNS.extendG (α n t)) ≤ R := by
    intro n
    have hp := TorusFourierNS.galerkin_hs_propagation hν hs hr2 (hder n) (hstr n) (hA n) t ht
    rw [h0 n] at hp
    have hres := TorusFourierNS.hsNormField_extendG_restrictG_le (periodicDataHs r u₀ hu₀) (N n)
    have hsq : TorusFourierNS.hsNormField r (TorusFourierNS.extendG (α n t)) ^ 2 ≤
        H ^ 2 * Real.exp (C * A * T) := by
      refine hp.trans ?_
      have he : Real.exp (C * A * t) ≤ Real.exp (C * A * T) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hC hA0))
      have := pow_le_pow_left₀ (TorusFourierNS.hsNormField_nonneg _ _) hres 2
      exact mul_le_mul this he (Real.exp_pos _).le (sq_nonneg _)
    refine (hsNormField_extendG_mono (r := r) (le_max_left _ _) _).trans ?_
    exact Real.le_sqrt_of_sq_le hsq
  exact hs_of_tendsto hbd (hlim t ht)

/-- **Proved.** `PeriodicGalerkinLimit` from the remaining named sub-Props (`0 ≤ ν`, `5/2 < s`). -/
theorem periodicGalerkinLimit_of_subProps'' {ν s : ℝ} (hν : 0 ≤ ν) (hs : 5 / 2 < s)
    (hG : FourierGalerkinApproximation ν s) (hV : FourierSeriesVelocitySmooth ν)
    (hP : PeriodicPressureRecovery ν) : PeriodicGalerkinLimit ν s :=
  periodicGalerkinLimit_of_subProps' (by linarith) (fourierHigherRegularity_of hν hs hG) hV hP

end PeriodicNSContinuation
