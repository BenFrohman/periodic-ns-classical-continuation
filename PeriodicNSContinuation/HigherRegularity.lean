/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.FourierInversion
import TorusFourierNS.TameTransport
import PeriodicNSContinuation.GalerkinLimitProof

/-!
# Propagation of higher regularity via the tame Galerkin estimate

**Proved:** `hs_bound_of_galerkin (0 ≤ ν) (5/2 < s)`: a mode-wise limit of Galerkin solutions from
smooth data with a uniform `H^s` bound is bounded in every `H^{s'}`. The proof uses the tame Galerkin
bound `galerkin_hs_propagation` (torus-fourier-ns-lemmas) at `r = max s' 2`, then
`hsNormField_extendG_restrictG_le`, and Fatou (`hs_of_tendsto`).

**Proved:** `periodicGalerkinLimit_of_velocity_pressure (0 ≤ ν) (5/2 < s)`:
`FourierSeriesVelocitySmooth ν → PeriodicPressureRecovery ν → PeriodicGalerkinLimit ν s`.
Reconstruction is applied to the constructed Galerkin subsequence limit, so the earlier
`FourierGalerkinApproximation` Prop is no longer needed and has been removed.
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D

namespace PeriodicNSContinuation

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

/-- **Proved (`ν ≥ 0`, `5/2 < s`).** Every `H^{s'}` bound for a mode-wise limit of Galerkin
solutions from smooth data that stay Hermitian, divergence-free and bounded in `H^s`. -/
theorem hs_bound_of_galerkin {ν s : ℝ} (hν : 0 ≤ ν) (hs : 5 / 2 < s)
    {u₀ : NavierStokes3D.VelocityField} (hu₀ : IsPeriodicSmoothInitialData u₀) {T : ℝ} (hT : 0 < T)
    {N : ℕ → ℕ} {α : ∀ n, ℝ → TorusFourierNS.GState (N n)} {A : ℝ}
    {a : ℝ → TorusFourierNS.FField}
    (h0 : ∀ n, α n 0 = TorusFourierNS.restrictG (N n) (fourierCoeffVF u₀))
    (hder : ∀ n, ∀ t ∈ Icc 0 T,
      HasDerivAt (α n) (TorusFourierNS.galerkinNSField (N n) ν (α n t)) t)
    (hstr : ∀ n, ∀ t ∈ Icc 0 T, TorusFourierNS.HermitianField (TorusFourierNS.extendG (α n t)) ∧
      TorusFourierNS.DivergenceFree (TorusFourierNS.extendG (α n t)))
    (hA : ∀ n, ∀ t ∈ Icc 0 T, TorusFourierNS.hsNormField s (TorusFourierNS.extendG (α n t)) ≤ A)
    (hlim : ∀ t ∈ Icc 0 T, ∀ k i,
      Tendsto (fun n => TorusFourierNS.extendG (α n t) k i) atTop (𝓝 (a t k i)))
    (s' : ℝ) : ∃ R : ℝ, ∀ t ∈ Icc 0 T, TorusFourierNS.MemHsField s' (a t) ∧
      TorusFourierNS.hsNormField s' (a t) ≤ R := by
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

/-- **Proved (`ν ≥ 0`, `5/2 < s`).** `PeriodicGalerkinLimit` from `FourierSeriesVelocitySmooth` and
`PeriodicPressureRecovery` alone. The reconstruction is applied to the constructed Galerkin
subsequence limit, whose approximation data gives every `H^{s'}` bound (`hs_bound_of_galerkin`). -/
theorem periodicGalerkinLimit_of_velocity_pressure {ν s : ℝ} (hν : 0 ≤ ν) (hs : 5 / 2 < s)
    (hV : FourierSeriesVelocitySmooth ν) (hP : PeriodicPressureRecovery ν) :
    PeriodicGalerkinLimit ν s := by
  have hs2 : 2 < s := by linarith
  intro u₀ hu₀ T hT ⟨M, hM⟩
  choose α hαs hαb using hM
  obtain ⟨φ, hφ, a, hconv⟩ :=
    galerkinModeConvergence_of (galerkinModeEquiLipschitz hs2) u₀ hu₀ T hT M α hαs hαb
  have hstr := galerkinStructurePreserved_of ν periodicDataDivFree u₀ hu₀
  have h0 : a 0 = fourierCoeffVF u₀ := limit_initial hαs hφ (hconv 0 ⟨le_rfl, hT.le⟩)
  have heq := galerkinLimitEquation hs2 u₀ hu₀ T hT M α hαs hαb φ hφ a hconv
  have hstrA : ∀ t ∈ Icc 0 T, TorusFourierNS.HermitianField (a t) ∧
      TorusFourierNS.DivergenceFree (a t) := fun t ht =>
    ⟨hermitian_of_tendsto (fun n => (hstr (φ n) T (α (φ n)) (hαs (φ n)) t ht).1) (hconv t ht),
     divergenceFree_of_tendsto (fun n => (hstr (φ n) T (α (φ n)) (hαs (φ n)) t ht).2) (hconv t ht)⟩
  have hsm : IsSmoothFourierSolutionOn ν u₀ T a :=
    ⟨h0, fun s' => hs_bound_of_galerkin (N := φ) (α := fun n => α (φ n)) hν hs hu₀ hT
      (fun n => (hαs (φ n)).1) (fun n => (hαs (φ n)).2)
      (fun n => hstr (φ n) T (α (φ n)) (hαs (φ n))) (fun n => hαb (φ n)) hconv s', hstrA, heq⟩
  obtain ⟨hVc, hVd, hV0⟩ := fourierSeriesVelocity_of hV u₀ hu₀ T hT a hsm
  obtain ⟨hPc, hPe⟩ := hP u₀ hu₀ T hT a hsm
  exact ⟨seriesVelocity a, seriesPressure a, hT, fun t _ => seriesVelocity_periodic a t,
    fun t _ => seriesPressure_periodic a t, hVc, hPc, hPe, hVd, hV0⟩

end PeriodicNSContinuation
