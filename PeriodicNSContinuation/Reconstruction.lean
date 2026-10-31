/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.GalerkinLimitProof

/-!
# Splitting `FourierSolutionReconstruction`

`FourierSolutionReconstruction ν s` is split into three named sub-Props (all coined, **NOT proved**):

* `FourierHigherRegularity ν s`: an `H^s` Fourier solution from smooth data is bounded in
  `H^{s'}` on `[0,T]` for every `s'`.
* `FourierSeriesVelocity ν`: for such a rapidly decaying solution, the inverse Fourier series
  `seriesVelocity a` is jointly `C^∞` on `[0,T] × ℝ³`, divergence-free, and equal to `u₀` at `t = 0`.
* `PeriodicPressureRecovery ν`: the pressure `seriesPressure a` (Fourier coefficients
  `pressureCoeff`) is jointly `C^∞`, and `(seriesVelocity a, seriesPressure a)` satisfy the
  momentum equation.

**Proved:** `fourierSolutionReconstruction_of` (the three Props imply
`FourierSolutionReconstruction`); periodicity of both series for *any* coefficients
(`seriesVelocity_periodic`, `seriesPressure_periodic`), so periodicity is not an assumption; and the
Fourier-side pressure identity `fourierNSField_eq_pressure`:
`fourierNSField ν a k i = -visc·a k i - N̂ k i - 2πi kᵢ p̂ k`, the Fourier form of
`∂ₜu + (u·∇)u = νΔu - ∇p`.
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D
open scoped ContDiff

namespace PeriodicNSContinuation

/-- Fourier character `e^{2πi k·x}` (coined). -/
def phase (k : TorusFourierNS.Mode) (x : T3) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ∑ j, ((k j : ℝ) : ℂ) * ((x j : ℝ) : ℂ))

/-- Inverse Fourier series of a coefficient family (coined). -/
def seriesC (b : TorusFourierNS.Mode → ℂ) (x : T3) : ℂ := ∑' k, b k * phase k x

/-- Velocity reconstructed from Fourier coefficients (real part, componentwise) (coined). -/
def seriesVelocity (a : ℝ → TorusFourierNS.FField) : TimeDependentVelocity := fun t x =>
  (EuclideanSpace.equiv (Fin 3) ℝ).symm fun i => (seriesC (fun k => a t k i) x).re

/-- Fourier coefficients of `(u·∇)u` (coined). -/
def nonlinCoeff (a : TorusFourierNS.FField) (k : TorusFourierNS.Mode) : Fin 3 → ℂ := fun j =>
  2 * Real.pi * Complex.I * ∑' m, convTerm a k m j

/-- Pressure coefficient `p̂ = -(k·ŵ) / (2πi |k|²)` (coined). -/
def pressureCoeff (k : TorusFourierNS.Mode) (w : Fin 3 → ℂ) : ℂ :=
  -TorusFourierNS.dot (TorusFourierNS.kvec k) w /
    (2 * Real.pi * Complex.I * (TorusFourierNS.ksq (TorusFourierNS.kvec k) : ℂ))

/-- Pressure reconstructed from Fourier coefficients (coined). -/
def seriesPressure (a : ℝ → TorusFourierNS.FField) : TimeDependentPressure := fun t x =>
  (seriesC (fun k => pressureCoeff k (nonlinCoeff (a t) k)) x).re

/-- Hypotheses of `FourierSolutionReconstruction` (coined). -/
def IsFourierSolutionOn (ν s M : ℝ) (u₀ : NavierStokes3D.VelocityField) (T : ℝ)
    (a : ℝ → TorusFourierNS.FField) : Prop :=
  a 0 = fourierCoeffVF u₀ ∧
  (∀ t ∈ Icc 0 T, TorusFourierNS.MemHsField s (a t) ∧
    TorusFourierNS.hsNormField s (a t) ≤ M ∧ TorusFourierNS.HermitianField (a t) ∧
    TorusFourierNS.DivergenceFree (a t)) ∧
  (∀ t ∈ Icc 0 T, ∀ k i, a t k i = a 0 k i + ∫ τ in (0 : ℝ)..t, fourierNSField ν (a τ) k i)

/-- A Fourier solution bounded in every `H^{s'}` (coined). -/
def IsSmoothFourierSolutionOn (ν : ℝ) (u₀ : NavierStokes3D.VelocityField) (T : ℝ)
    (a : ℝ → TorusFourierNS.FField) : Prop :=
  a 0 = fourierCoeffVF u₀ ∧
  (∀ s' : ℝ, ∃ M' : ℝ, ∀ t ∈ Icc 0 T, TorusFourierNS.MemHsField s' (a t) ∧
    TorusFourierNS.hsNormField s' (a t) ≤ M') ∧
  (∀ t ∈ Icc 0 T, TorusFourierNS.HermitianField (a t) ∧ TorusFourierNS.DivergenceFree (a t)) ∧
  (∀ t ∈ Icc 0 T, ∀ k i, a t k i = a 0 k i + ∫ τ in (0 : ℝ)..t, fourierNSField ν (a τ) k i)

/-- **NOT proved** (coined). Propagation of higher regularity. -/
def FourierHigherRegularity (ν s : ℝ) : Prop :=
  ∀ u₀ : NavierStokes3D.VelocityField, IsPeriodicSmoothInitialData u₀ → ∀ T : ℝ, 0 < T →
    ∀ (M : ℝ) (a : ℝ → TorusFourierNS.FField), IsFourierSolutionOn ν s M u₀ T a →
      ∀ s' : ℝ, ∃ M' : ℝ, ∀ t ∈ Icc 0 T, TorusFourierNS.MemHsField s' (a t) ∧
        TorusFourierNS.hsNormField s' (a t) ≤ M'

/-- **NOT proved** (coined). The inverse Fourier series gives a smooth velocity. -/
def FourierSeriesVelocity (ν : ℝ) : Prop :=
  ∀ u₀ : NavierStokes3D.VelocityField, IsPeriodicSmoothInitialData u₀ → ∀ T : ℝ, 0 < T →
    ∀ a : ℝ → TorusFourierNS.FField, IsSmoothFourierSolutionOn ν u₀ T a →
      ContDiffOn ℝ ∞ (fun q : ℝ × T3 => seriesVelocity a q.1 q.2) (Icc (0 : ℝ) T ×ˢ univ) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x : T3, div (seriesVelocity a t) x = 0) ∧
      (∀ x : T3, seriesVelocity a 0 x = u₀ x)

/-- **NOT proved** (coined). Pressure recovery and the momentum equation. -/
def PeriodicPressureRecovery (ν : ℝ) : Prop :=
  ∀ u₀ : NavierStokes3D.VelocityField, IsPeriodicSmoothInitialData u₀ → ∀ T : ℝ, 0 < T →
    ∀ a : ℝ → TorusFourierNS.FField, IsSmoothFourierSolutionOn ν u₀ T a →
      ContDiffOn ℝ ∞ (fun q : ℝ × T3 => seriesPressure a q.1 q.2) (Icc (0 : ℝ) T ×ˢ univ) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x : T3,
        derivWithin (fun s => seriesVelocity a s x) (Icc (0 : ℝ) T) t +
            convective (seriesVelocity a t) (seriesVelocity a t) x =
          ν • laplacian (seriesVelocity a t) x - pressureGradient (seriesPressure a t) x +
            (fun _ _ => (0 : EuclideanSpace ℝ (Fin 3))) t x)

/-- **Proved.** `e^{2πi k·x}` is `ℤ³`-periodic. -/
lemma phase_periodic (k : TorusFourierNS.Mode) : IsZ3Periodic (phase k) := by
  intro x n
  have hx : ∀ j, (x + intVecToT3 n) j = x j + (n j : ℝ) := fun j => by
    simp [intVecToT3, stdBasisVec, Pi.single_apply]
  unfold phase
  simp only [hx]
  have : ∑ j, ((k j : ℝ) : ℂ) * (((x j + (n j : ℝ)) : ℝ) : ℂ) =
      ∑ j, ((k j : ℝ) : ℂ) * ((x j : ℝ) : ℂ) + ((∑ j, k j * n j : ℤ) : ℂ) := by
    push_cast; rw [← Finset.sum_add_distrib]; congr 1; funext j; ring
  rw [this, mul_add, Complex.exp_add]
  have h1 : Complex.exp (2 * Real.pi * Complex.I * ((∑ j, k j * n j : ℤ) : ℂ)) = 1 := by
    rw [show 2 * Real.pi * Complex.I * ((∑ j, k j * n j : ℤ) : ℂ) =
      ((∑ j, k j * n j : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [h1, mul_one]

/-- **Proved.** Any inverse Fourier series is `ℤ³`-periodic. -/
lemma seriesC_periodic (b : TorusFourierNS.Mode → ℂ) : IsZ3Periodic (seriesC b) := by
  intro x n; unfold seriesC; simp only [phase_periodic _ x n]

/-- **Proved.** The reconstructed velocity is periodic, for any coefficients. -/
theorem seriesVelocity_periodic (a : ℝ → TorusFourierNS.FField) (t : ℝ) :
    IsZ3Periodic (seriesVelocity a t) := by
  intro x n; unfold seriesVelocity; simp only [seriesC_periodic _ x n]

/-- **Proved.** The reconstructed pressure is periodic, for any coefficients. -/
theorem seriesPressure_periodic (a : ℝ → TorusFourierNS.FField) (t : ℝ) :
    IsZ3Periodic (seriesPressure a t) := by
  intro x n; unfold seriesPressure; simp only [seriesC_periodic _ x n]

/-- **Proved.** `conj (e^{2πi k·x}) = e^{2πi (-k)·x}`. -/
lemma conj_phase (k : TorusFourierNS.Mode) (x : T3) :
    (starRingEnd ℂ) (phase k x) = phase (-k) x := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_sum, Complex.conj_ofReal, Complex.conj_I, map_ofNat, Pi.neg_apply,
    Int.cast_neg, Complex.ofReal_neg, neg_mul, Finset.sum_neg_distrib]
  ring

/-- **Proved.** Hermitian coefficients give a real series: `conj (seriesC b x) = seriesC b x`, so
taking the real part in `seriesVelocity` loses nothing. -/
theorem conj_seriesC_of_hermitian {b : TorusFourierNS.Mode → ℂ}
    (hb : ∀ k, b (-k) = (starRingEnd ℂ) (b k)) (x : T3) :
    (starRingEnd ℂ) (seriesC b x) = seriesC b x := by
  unfold seriesC
  rw [Complex.conj_tsum]
  have : ∀ k, (starRingEnd ℂ) (b k * phase k x) = b (-k) * phase (-k) x := fun k => by
    rw [map_mul, conj_phase, hb]
  simp only [this]
  exact (Equiv.neg TorusFourierNS.Mode).tsum_eq (fun k => b k * phase k x)

/-- **Proved.** Leray decomposition with the pressure coefficient:
`-(P w)ᵢ = -wᵢ - 2πi kᵢ p̂(k, w)`. -/
theorem neg_lerayP_eq (k : TorusFourierNS.Mode) (w : Fin 3 → ℂ) (i : Fin 3) :
    -TorusFourierNS.lerayP k w i =
      -w i - 2 * Real.pi * Complex.I * (TorusFourierNS.kvec k i : ℂ) * pressureCoeff k w := by
  unfold TorusFourierNS.lerayP pressureCoeff
  set q := TorusFourierNS.ksq (TorusFourierNS.kvec k)
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  by_cases hq : q = 0
  · have hi : TorusFourierNS.kvec k i = 0 := by
      have := Finset.single_le_sum (f := fun l => TorusFourierNS.kvec k l ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
      have hqd : q = ∑ x, TorusFourierNS.kvec k x ^ 2 := rfl
      simp only at this
      nlinarith [sq_nonneg (TorusFourierNS.kvec k i)]
    simp [hq, hi]
  · have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast hq
    field_simp
    ring

/-- **Proved.** Fourier form of `∂ₜu + (u·∇)u = νΔu - ∇p` with `p̂ = pressureCoeff`. -/
theorem fourierNSField_eq_pressure (ν : ℝ) (a : TorusFourierNS.FField) (k : TorusFourierNS.Mode)
    (i : Fin 3) :
    fourierNSField ν a k i = -((TorusFourierNS.viscCoeff ν k : ℝ) : ℂ) * a k i -
      nonlinCoeff a k i -
      2 * Real.pi * Complex.I * (TorusFourierNS.kvec k i : ℂ) * pressureCoeff k (nonlinCoeff a k) := by
  have := neg_lerayP_eq k (nonlinCoeff a k) i
  unfold fourierNSField
  change _ - TorusFourierNS.lerayP k (nonlinCoeff a k) i = _
  rw [sub_eq_add_neg _ (TorusFourierNS.lerayP _ _ _), this]
  ring

/-- **Proved.** The three sub-Props give `FourierSolutionReconstruction`. -/
theorem fourierSolutionReconstruction_of {ν s : ℝ} (hR : FourierHigherRegularity ν s)
    (hV : FourierSeriesVelocity ν) (hP : PeriodicPressureRecovery ν) :
    FourierSolutionReconstruction ν s := by
  intro u₀ hu₀ T hT M a h0 hbd heq
  have hsol : IsFourierSolutionOn ν s M u₀ T a := ⟨h0, hbd, heq⟩
  have hsm : IsSmoothFourierSolutionOn ν u₀ T a :=
    ⟨h0, hR u₀ hu₀ T hT M a hsol, fun t ht => ⟨(hbd t ht).2.2.1, (hbd t ht).2.2.2⟩, heq⟩
  obtain ⟨hVc, hVd, hV0⟩ := hV u₀ hu₀ T hT a hsm
  obtain ⟨hPc, hPe⟩ := hP u₀ hu₀ T hT a hsm
  exact ⟨seriesVelocity a, seriesPressure a, hT, fun t _ => seriesVelocity_periodic a t,
    fun t _ => seriesPressure_periodic a t, hVc, hPc, hPe, hVd, hV0⟩

/-- **Proved (conditional on the three sub-Props), for `s > 2`.** -/
theorem periodicGalerkinLimit_of_subProps {ν s : ℝ} (hs : 2 < s) (hR : FourierHigherRegularity ν s)
    (hV : FourierSeriesVelocity ν) (hP : PeriodicPressureRecovery ν) : PeriodicGalerkinLimit ν s :=
  periodicGalerkinLimit_of_reconstruction hs (fourierSolutionReconstruction_of hR hV hP)

end PeriodicNSContinuation
