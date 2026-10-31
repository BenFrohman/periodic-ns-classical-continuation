/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.Reconstruction
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# 3D Fourier inversion for smooth periodic data

**Proved:** `fourierCoeffVF_hasSum`: for smooth, periodic `u₀`, the series
`Σ_k fourierCoeffVF u₀ k i · e^{2πi k·x}` converges to `u₀ x i` at every `x`. Consequently
`seriesVelocity_zero`: if `a 0 = fourierCoeffVF u₀` then `seriesVelocity a 0 = u₀`.
The proof descends each component to a continuous function on `UnitAddTorus (Fin 3)`, identifies
Mathlib's `mFourierCoeff` with `fourierCoeffVF`, and gets summability of the coefficients from
`periodicDataHs 2` (`‖c‖ ≤ w⁻² + w²‖c‖²`). It then uses `hasSum_mFourier_series_apply_of_summable`.
All names are coined.
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D UnitAddTorus
open scoped ContDiff

namespace PeriodicNSContinuation

/-- Component of `u₀` as a function on `ℝ³ = Fin 3 → ℝ` (coined). -/
def compR (u₀ : NavierStokes3D.VelocityField) (i : Fin 3) (y : Fin 3 → ℝ) : ℂ :=
  ((u₀ ((EuclideanSpace.equiv (Fin 3) ℝ).symm y) i : ℝ) : ℂ)

/-- Quotient map `ℝ³ → 𝕋³` (coined). -/
def torusMk : (Fin 3 → ℝ) → UnitAddTorus (Fin 3) := Pi.map fun _ (r : ℝ) => (r : UnitAddCircle)

lemma isOpenQuotientMap_torusMk : IsOpenQuotientMap torusMk :=
  IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk

lemma torusMk_eq {y y' : Fin 3 → ℝ} (h : torusMk y = torusMk y') :
    ∃ n : Fin 3 → ℤ, y' = y + fun j => (n j : ℝ) := by
  have : ∀ j, ∃ n : ℤ, (n : ℝ) = -y j + y' j := fun j => by
    have hj := congrFun h j
    simp only [torusMk, Pi.map_apply] at hj
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq.1 hj)
    exact ⟨n, by simpa using hn⟩
  choose n hn using this
  exact ⟨n, funext fun j => by simp [hn j]⟩

lemma compR_periodic {u₀ : NavierStokes3D.VelocityField} (hp : IsZ3Periodic u₀) (i : Fin 3)
    (y : Fin 3 → ℝ) (n : Fin 3 → ℤ) : compR u₀ i (y + fun j => (n j : ℝ)) = compR u₀ i y := by
  unfold compR
  have : (EuclideanSpace.equiv (Fin 3) ℝ).symm (y + fun j => (n j : ℝ)) =
      (EuclideanSpace.equiv (Fin 3) ℝ).symm y + intVecToT3 n := by
    ext j; simp [intVecToT3, stdBasisVec, Pi.single_apply]
  rw [this, hp]

/-- Component of `u₀` on the torus (coined). -/
def torusComp (u₀ : NavierStokes3D.VelocityField) (i : Fin 3) : UnitAddTorus (Fin 3) → ℂ :=
  fun z => compR u₀ i (Function.surjInv isOpenQuotientMap_torusMk.surjective z)

lemma torusComp_mk {u₀ : NavierStokes3D.VelocityField} (hp : IsZ3Periodic u₀) (i : Fin 3)
    (y : Fin 3 → ℝ) : torusComp u₀ i (torusMk y) = compR u₀ i y := by
  unfold torusComp
  obtain ⟨n, hn⟩ := torusMk_eq
    (Function.surjInv_eq isOpenQuotientMap_torusMk.surjective (torusMk y))
  conv_rhs => rw [hn]
  exact (compR_periodic hp i _ n).symm

lemma continuous_compR {u₀ : NavierStokes3D.VelocityField} (hc : Continuous u₀) (i : Fin 3) :
    Continuous (compR u₀ i) := by
  unfold compR
  have h1 : Continuous fun y => u₀ ((EuclideanSpace.equiv (Fin 3) ℝ).symm y) :=
    hc.comp (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous
  have h2 : Continuous fun v : EuclideanSpace ℝ (Fin 3) => v i :=
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).continuous
  exact Complex.continuous_ofReal.comp (h2.comp h1)

/-- Continuous component on the torus (coined). -/
def torusCompC {u₀ : NavierStokes3D.VelocityField} (hu : IsPeriodicSmoothInitialData u₀)
    (i : Fin 3) : C(UnitAddTorus (Fin 3), ℂ) where
  toFun := torusComp u₀ i
  continuous_toFun := by
    refine isOpenQuotientMap_torusMk.isQuotientMap.continuous_iff.2 ?_
    have : torusComp u₀ i ∘ torusMk = compR u₀ i := funext (torusComp_mk hu.2.2 i)
    rw [this]
    exact continuous_compR hu.1.continuous i

lemma mFourier_torusMk (n : Fin 3 → ℤ) (y : Fin 3 → ℝ) :
    mFourier n (torusMk y) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ j, ((n j : ℝ) : ℂ) * ((y j : ℝ) : ℂ)) := by
  simp only [mFourier, ContinuousMap.coe_mk, torusMk, Pi.map_apply]
  simp only [fourier_coe_apply, Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum, Finset.mul_sum]
  congr 1; refine Finset.sum_congr rfl fun j _ => ?_
  push_cast; ring

/-- **Proved.** Mathlib's torus Fourier coefficient is `fourierCoeffVF`. -/
theorem mFourierCoeff_torusCompC {u₀ : NavierStokes3D.VelocityField}
    (hu : IsPeriodicSmoothInitialData u₀) (i : Fin 3) (n : Fin 3 → ℤ) :
    mFourierCoeff (torusCompC hu i) n = fourierCoeffVF u₀ n i := by
  rw [mFourierCoeff_eq_integral _ n 0]
  have hset : {x : Fin 3 → ℝ | ∀ j, x j ∈ Ioc ((0 : Fin 3 → ℝ) j) ((0 : Fin 3 → ℝ) j + 1)} =
      univ.pi fun _ => Ioc (0 : ℝ) 1 := by ext x; simp
  have hae : (univ.pi fun _ => Ioc (0 : ℝ) 1) =ᵐ[(MeasureTheory.volume : Measure (Fin 3 → ℝ))] Icc (0 : Fin 3 → ℝ) 1 := by
    rw [volume_pi]
    exact Measure.univ_pi_Ioc_ae_eq_Icc (f := fun _ => (0 : ℝ)) (g := fun _ => (1 : ℝ))
  rw [hset, setIntegral_congr_set hae]
  unfold fourierCoeffVF
  refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
  have h1 : (fun j => ((x j : ℝ) : UnitAddCircle)) = torusMk x := rfl
  have h2 : (torusCompC hu i) (torusMk x) = compR u₀ i x := torusComp_mk hu.2.2 i x
  simp only [h1, h2, mFourier_torusMk, smul_eq_mul, compR]
  rw [mul_comm]
  congr 2
  simp only [Pi.neg_apply, Int.cast_neg, Complex.ofReal_neg, neg_mul, Finset.sum_neg_distrib]
  ring

/-- **Proved.** `‖c‖ ≤ w⁻² + w² ‖c‖²` for `w ≥ 1`... in fact for any `w > 0`. -/
lemma norm_le_aux {c A : ℝ} (hc : 0 ≤ c) (hA : 0 < A) : c ≤ A⁻¹ + A * c ^ 2 := by
  by_cases h : c ≤ A⁻¹
  · nlinarith [mul_nonneg hA.le (sq_nonneg c)]
  · push Not at h
    have : 1 < A * c := by rwa [inv_lt_iff_one_lt_mul₀' hA] at h
    have hA' := inv_pos.2 hA
    nlinarith

/-- **Proved.** Fourier coefficients of smooth periodic data are absolutely summable. -/
theorem summable_norm_fourierCoeffVF {u₀ : NavierStokes3D.VelocityField}
    (hu : IsPeriodicSmoothInitialData u₀) (i : Fin 3) :
    Summable fun k => ‖fourierCoeffVF u₀ k i‖ := by
  have hH := periodicDataHs 2 u₀ hu
  unfold TorusFourierNS.MemHsField at hH
  have hHi : Summable fun k : TorusFourierNS.Mode =>
      TorusFourierNS.sobW 2 k * ‖fourierCoeffVF u₀ k i‖ ^ 2 :=
    hH.comp_injective (i := fun k => (k, i)) fun a b h => by simpa using h
  have hneg := TorusFourierNS.summable_sobW_neg (s := 2) (by norm_num)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) (hneg.add hHi)
  have hA : 0 < TorusFourierNS.sobW 2 k := Real.rpow_pos_of_pos (TorusFourierNS.one_add_sq_pos k) _
  have : TorusFourierNS.sobW (-2) k = (TorusFourierNS.sobW 2 k)⁻¹ :=
    Real.rpow_neg (TorusFourierNS.one_add_sq_pos k).le _
  rw [this]
  exact norm_le_aux (norm_nonneg _) hA

/-- **Proved.** 3D Fourier inversion for smooth periodic data, pointwise. -/
theorem fourierCoeffVF_hasSum {u₀ : NavierStokes3D.VelocityField}
    (hu : IsPeriodicSmoothInitialData u₀) (i : Fin 3) (x : T3) :
    HasSum (fun k => fourierCoeffVF u₀ k i * phase k x) ((u₀ x i : ℝ) : ℂ) := by
  have hsum : Summable (mFourierCoeff (torusCompC hu i)) := by
    have : mFourierCoeff (torusCompC hu i) = fun k => fourierCoeffVF u₀ k i :=
      funext (mFourierCoeff_torusCompC hu i)
    rw [this]; exact (summable_norm_fourierCoeffVF hu i).of_norm
  have h := hasSum_mFourier_series_apply_of_summable hsum
    (torusMk (EuclideanSpace.equiv (Fin 3) ℝ x))
  have hv : (torusCompC hu i) (torusMk (EuclideanSpace.equiv (Fin 3) ℝ x)) = ((u₀ x i : ℝ) : ℂ) := by
    change torusComp u₀ i _ = _
    rw [torusComp_mk hu.2.2]; simp [compR]
  rw [hv] at h
  convert h using 2 with k
  rw [mFourierCoeff_torusCompC, smul_eq_mul, mFourier_torusMk]
  rfl

/-- **Proved.** The reconstructed velocity has the right initial value. -/
theorem seriesVelocity_zero {u₀ : NavierStokes3D.VelocityField}
    (hu : IsPeriodicSmoothInitialData u₀) {a : ℝ → TorusFourierNS.FField}
    (h0 : a 0 = fourierCoeffVF u₀) (x : T3) : seriesVelocity a 0 x = u₀ x := by
  ext i
  simp only [seriesVelocity, seriesC, h0]
  change (∑' (k : TorusFourierNS.Mode), fourierCoeffVF u₀ k i * phase k x).re = _
  rw [(fourierCoeffVF_hasSum hu i x).tsum_eq]
  simp

/-- **NOT proved** (coined). The smoothness and divergence-free parts of `FourierSeriesVelocity`,
which are what remains of it once the initial-value clause is proved (`seriesVelocity_zero`). -/
def FourierSeriesVelocitySmooth (ν : ℝ) : Prop :=
  ∀ u₀ : NavierStokes3D.VelocityField, IsPeriodicSmoothInitialData u₀ → ∀ T : ℝ, 0 < T →
    ∀ a : ℝ → TorusFourierNS.FField, IsSmoothFourierSolutionOn ν u₀ T a →
      ContDiffOn ℝ ∞ (fun q : ℝ × T3 => seriesVelocity a q.1 q.2) (Icc (0 : ℝ) T ×ˢ univ) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x : T3, div (seriesVelocity a t) x = 0)

/-- **Proved.** `FourierSeriesVelocity ν` from `FourierSeriesVelocitySmooth ν`. -/
theorem fourierSeriesVelocity_of {ν : ℝ} (h : FourierSeriesVelocitySmooth ν) :
    FourierSeriesVelocity ν := fun u₀ hu T hT a ha =>
  ⟨(h u₀ hu T hT a ha).1, (h u₀ hu T hT a ha).2, seriesVelocity_zero hu ha.1⟩

/-- **Proved.** `PeriodicGalerkinLimit` from the remaining sub-Props. -/
theorem periodicGalerkinLimit_of_subProps' {ν s : ℝ} (hs : 2 < s) (hR : FourierHigherRegularity ν s)
    (hV : FourierSeriesVelocitySmooth ν) (hP : PeriodicPressureRecovery ν) :
    PeriodicGalerkinLimit ν s :=
  periodicGalerkinLimit_of_subProps hs hR (fourierSeriesVelocity_of hV) hP

end PeriodicNSContinuation
