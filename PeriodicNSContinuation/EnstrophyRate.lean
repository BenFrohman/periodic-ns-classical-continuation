/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.EnstrophyIdentity

/-!
# Reducing `PeriodicEnstrophyRateBound` to the Ladyzhenskaya trilinear estimate

* `young_absorb` — **proved** (real analysis): from `N⁴ ≤ K X³E³` we get `N ≤ (c/2) X + (8K/c³) E³`.
* `visc_term_le_H2` — **proved**: for a zero mode coefficient or `k ≠ 0`, the `H¹` viscous term is
  `≤ −4π²ν (1+|k|²)² |a_k|²` (Poincaré on nonzero modes).
* `periodicEnstrophyRateBound_of_trilinear` — **proved** from two named Props:
  - `PeriodicH1TrilinearBound K` (coined; not formalized). For smooth zero-mean `v`, the
    nonlinear `H¹` rate is summable and `max(N,0)⁴ ≤ K ‖v‖_{H²}⁶ ‖v‖_{H¹}⁶`, where
    `‖v‖²_{H²} = hsSq 2`. This is the classical consequence of Ladyzhenskaya
    `‖f‖_{L⁴} ≲ ‖f‖^{1/4}_{L²}‖∇f‖^{3/4}_{L²}` through `|⟨Δu, u·∇u⟩| ≤ ‖Δu‖ ‖u‖_{L⁴}‖∇u‖_{L⁴}`.
  - `PeriodicMeanConservation ν` (coined; not formalized). Zero-mean data stay zero-mean.
  Along the way it uses the proved Fourier coefficient decay. The resulting constants are
  `α = 2π²ν` and `β = 8K/(4π²ν)³`.
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D TorusFourierNS

namespace PeriodicNSContinuation

open Corrected

/-- **Proved.** Young-type absorption. -/
theorem young_absorb {N X E K c : ℝ} (hX : 0 ≤ X) (hE : 0 ≤ E) (hK : 0 ≤ K) (hc : 0 < c)
    (h : max N 0 ^ 4 ≤ K * X ^ 3 * E ^ 3) : N ≤ c / 2 * X + 8 * K / c ^ 3 * E ^ 3 := by
  by_contra hcon
  push Not at hcon
  have hβ : 0 ≤ 8 * K / c ^ 3 * E ^ 3 := by positivity
  have h1 : c / 2 * X < N := by nlinarith [mul_nonneg hc.le hX]
  have h2 : 8 * K / c ^ 3 * E ^ 3 < N := by nlinarith [mul_nonneg hc.le hX]
  have hN : 0 < N := lt_of_le_of_lt hβ h2
  rw [max_eq_left hN.le] at h
  have hA : 0 ≤ c / 2 * X := by positivity
  have h3 : (c / 2 * X) ^ 3 ≤ N ^ 3 := pow_le_pow_left₀ hA h1.le 3
  have h4 : (c / 2 * X) ^ 3 * (8 * K / c ^ 3 * E ^ 3) ≤ N ^ 3 * N := by
    rcases eq_or_lt_of_le hβ with h0 | h0
    · rw [← h0, mul_zero]; positivity
    · exact mul_le_mul h3 h2.le h0.le (by positivity)
  have h5 : (c / 2 * X) ^ 3 * (8 * K / c ^ 3 * E ^ 3) = K * X ^ 3 * E ^ 3 := by
    field_simp; ring
  rw [h5] at h4
  -- strictness: if K X³E³ = N⁴ is impossible since N > βE³ ≥ 0 and N > (c/2)X
  have hstrict : (c / 2 * X) ^ 3 * (8 * K / c ^ 3 * E ^ 3) < N ^ 3 * N := by
    rcases eq_or_lt_of_le hA with hA0 | hA0
    · rw [← hA0]; simp; positivity
    · exact mul_lt_mul' h3 h2 hβ (by positivity)
  rw [h5] at hstrict
  nlinarith [pow_succ N 3]

lemma one_le_ksq_of_ne {k : Mode} (hk : k ≠ 0) : 1 ≤ ksq (kvec k) := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h; push Not at h; exact hk (funext h)
  have h1 : (1:ℝ) ≤ (k i : ℝ) ^ 2 := by
    have : (1:ℤ) ≤ k i ^ 2 := by nlinarith [sq_nonneg (k i), Int.one_le_abs hi, sq_abs (k i)]
    exact_mod_cast this
  unfold ksq kvec
  calc (1:ℝ) ≤ (k i : ℝ) ^ 2 := h1
    _ ≤ ∑ j, ((k j : ℤ) : ℝ) ^ 2 :=
      Finset.single_le_sum (f := fun j => ((k j : ℤ) : ℝ) ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ i)

lemma sobW_one_eq (k : Mode) : sobW 1 k = 1 + ksq (kvec k) := by
  simp [sobW, ksq, kvec]

lemma sobW_two_eq (k : Mode) : sobW 2 k = (1 + ksq (kvec k)) ^ 2 := by
  rw [sobW, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; simp [ksq, kvec]

/-- **Proved.** Viscous `H¹` term against the `H²` weight (Poincaré on nonzero modes). -/
lemma visc_term_le_H2 {ν : ℝ} (hν : 0 ≤ ν) (a : FField) (k : Mode) (i : Fin 3)
    (hk : k ≠ 0 ∨ a k i = 0) :
    sobW 1 k * (2 * ((starRingEnd ℂ) (a k i) * (-((viscCoeff ν k : ℝ) : ℂ) * a k i)).re) ≤
      -(4 * Real.pi ^ 2 * ν) * (sobW 2 k * ‖a k i‖ ^ 2) := by
  have : ((starRingEnd ℂ) (a k i) * (-((viscCoeff ν k : ℝ) : ℂ) * a k i)).re =
      -(viscCoeff ν k * ‖a k i‖ ^ 2) := by
    rw [show (starRingEnd ℂ) (a k i) * (-((viscCoeff ν k : ℝ) : ℂ) * a k i) =
        -((viscCoeff ν k : ℝ) : ℂ) * ((starRingEnd ℂ) (a k i) * a k i) by ring,
      Complex.conj_mul']
    simp [← Complex.ofReal_pow]
  rw [this, sobW_one_eq, sobW_two_eq]
  unfold viscCoeff
  set n := ksq (kvec k)
  have hn0 : 0 ≤ n := by simp only [n, ksq]; positivity
  have hp : 0 ≤ Real.pi ^ 2 * ν := by positivity
  rcases hk with hk | hk
  · have hn := one_le_ksq_of_ne hk
    have : (1 + n) ^ 2 ≤ 2 * (1 + n) * n := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hp (sq_nonneg ‖a k i‖))]
  · simp [hk]

/-- Coined. **Hypothesis (classical, Ladyzhenskaya; not formalized).** -/
def PeriodicH1TrilinearBound (K : ℝ) : Prop :=
  ∀ v : VelocityField, IsPeriodicSmoothInitialData v → (∀ i, fourierCoeffVF v 0 i = 0) →
    Summable (fun p : Mode × Fin 3 => sobW 1 p.1 *
        (2 * ((starRingEnd ℂ) (fourierCoeffVF v p.1 p.2) * nlField (fourierCoeffVF v) p.1 p.2).re)) ∧
    max (rateOf 1 (nlField (fourierCoeffVF v)) (fourierCoeffVF v)) 0 ^ 4 ≤
      K * hsSq 2 v ^ 3 * hsSq 1 v ^ 3

/-- Coined. **Hypothesis (true, classical; not formalized).** The mean mode is conserved. -/
def PeriodicMeanConservation (ν : ℝ) : Prop :=
  0 < ν → ∀ (u₀ : VelocityField) (u : TimeDependentVelocity) (p : TimeDependentPressure) (T' : ℝ),
    IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T' u p → (∀ i, fourierCoeffVF u₀ 0 i = 0) →
    ∀ t ∈ Icc 0 T', ∀ i, fourierCoeffVF (u t) 0 i = 0

lemma hsSq_one_le_two {v : VelocityField} (hs : Summable fun p : Mode × Fin 3 =>
    sobW 2 p.1 * ‖fourierCoeffVF v p.1 p.2‖ ^ 2) : hsSq 1 v ≤ hsSq 2 v := by
  rw [hsSq_eq_tsum, hsSq_eq_tsum]
  refine Summable.tsum_le_tsum (fun p => ?_) (hs.of_nonneg_of_le
    (fun p => mul_nonneg (sobW_pos _ _).le (sq_nonneg _)) fun p => ?_) hs <;>
  · have : sobW 1 p.1 ≤ sobW 2 p.1 := by
      rw [sobW_one_eq, sobW_two_eq]; have : 0 ≤ ksq (kvec p.1) := by unfold ksq; positivity
      nlinarith
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

/-- **Proved** from the trilinear bound and mean conservation. -/
theorem periodicEnstrophyRateBound_of_trilinear {ν K : ℝ} (hK : 0 ≤ K)
    (hT : PeriodicH1TrilinearBound K) (hM : PeriodicMeanConservation ν) :
    PeriodicEnstrophyRateBound ν (2 * Real.pi ^ 2 * ν) (8 * K / (4 * Real.pi ^ 2 * ν) ^ 3) := by
  intro hν u₀ u p T' hsol hmean t ht
  have htI : t ∈ Icc (0:ℝ) T' := Ioo_subset_Icc_self ht
  have hut : IsPeriodicSmoothInitialData (u t) :=
    ⟨contDiff_slice hsol.2.2.2.1 htI, fun z => hsol.2.2.2.2.2.2.1 t htI z, hsol.2.1 t htI⟩
  have hmt := hM hν u₀ u p T' hsol hmean t htI
  obtain ⟨hnl, hbound⟩ := hT (u t) hut hmt
  obtain ⟨-, hder⟩ := periodicEnstrophyIdentity ν hν u₀ u p T' hsol
  obtain ⟨hsum, -⟩ := hder t ht
  set a := fourierCoeffVF (u t)
  -- H² summability from the proved decay
  obtain ⟨B, -, hB⟩ := periodicFourierCoeffDecay ν hν u₀ u p T' hsol 4
  have hs2 : Summable fun q : Mode × Fin 3 => sobW 2 q.1 * ‖a q.1 q.2‖ ^ 2 := by
    have hσ : 3 / 2 < -(2 + -4 + -4 : ℝ) := by norm_num
    have hsum0 : Summable fun k : Mode => 2 * B ^ 2 * sobW (2 + -4 + -4) k := by
      simpa using (summable_sobW_neg hσ).mul_left (2 * B ^ 2)
    have hU := summable_prod_fin3 (fun k => by have := sobW_pos (2 + -4 + -4 : ℝ) k; positivity) hsum0
    exact Summable.of_norm_bounded hU fun q => sq_term_le (s := 2) (hB t htI q.1 q.2).1
  have hsplit : ∀ q : Mode × Fin 3, sobW 1 q.1 *
      (2 * ((starRingEnd ℂ) (a q.1 q.2) * fourierNSField ν a q.1 q.2).re) =
      sobW 1 q.1 * (2 * ((starRingEnd ℂ) (a q.1 q.2) * (-((viscCoeff ν q.1 : ℝ) : ℂ) * a q.1 q.2)).re)
      + sobW 1 q.1 * (2 * ((starRingEnd ℂ) (a q.1 q.2) * nlField a q.1 q.2).re) := fun q => by
    rw [fourierNSField_eq, mul_add, Complex.add_re]; ring
  have hvs : Summable fun q : Mode × Fin 3 => sobW 1 q.1 *
      (2 * ((starRingEnd ℂ) (a q.1 q.2) * (-((viscCoeff ν q.1 : ℝ) : ℂ) * a q.1 q.2)).re) := by
    refine (hsum.sub hnl).congr fun q => ?_
    simp only [hsplit]; ring
  have hrate : rateOf 1 (fourierNSField ν a) a = (∑' q : Mode × Fin 3, sobW 1 q.1 *
      (2 * ((starRingEnd ℂ) (a q.1 q.2) * (-((viscCoeff ν q.1 : ℝ) : ℂ) * a q.1 q.2)).re))
      + rateOf 1 (nlField a) a := by
    unfold rateOf; rw [tsum_congr hsplit, hvs.tsum_add hnl]
  have hV : (∑' q : Mode × Fin 3, sobW 1 q.1 *
      (2 * ((starRingEnd ℂ) (a q.1 q.2) * (-((viscCoeff ν q.1 : ℝ) : ℂ) * a q.1 q.2)).re)) ≤
      -(4 * Real.pi ^ 2 * ν) * hsSq 2 (u t) := by
    rw [hsSq_eq_tsum, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun q => visc_term_le_H2 hν.le a q.1 q.2 ?_) hvs
      (hs2.mul_left _)
    by_cases hq : q.1 = 0
    · right; rw [hq]; exact hmt q.2
    · left; exact hq
  have hc : 0 < 4 * Real.pi ^ 2 * ν := by positivity
  have hY := young_absorb (hsSq_nonneg 2 (u t)) (hsSq_nonneg 1 (u t)) hK hc hbound
  have h12 := hsSq_one_le_two hs2
  have hE0 := hsSq_nonneg 1 (u t)
  show rateOf 1 (fourierNSField ν a) a ≤ h1Sq (u t) * _
  unfold h1Sq
  rw [hrate]
  have : -(4 * Real.pi ^ 2 * ν) * hsSq 2 (u t) ≤ -(4 * Real.pi ^ 2 * ν) * hsSq 1 (u t) :=
    mul_le_mul_of_nonpos_left h12 (by linarith)
  nlinarith

/-- **Proved** (conditional on the three named Props). Small zero-mean `H¹` data are global. -/
theorem periodicTstar_eq_top_of_smallH1_of_trilinear {ν K : ℝ} (hν : 0 < ν) (hK : 0 ≤ K)
    (hT : PeriodicH1TrilinearBound K) (hM : PeriodicMeanConservation ν)
    (hL : PeriodicH1BlowupCriterion ν) {u₀ : VelocityField} (hu₀ : IsPeriodicSmoothInitialData u₀)
    (hmean : ∀ i, fourierCoeffVF u₀ 0 i = 0) {u : TimeDependentVelocity} {p : TimeDependentPressure} (hm : IsPeriodicMaximalSolution ν u₀ u p)
    (hsmall : 8 * K / (4 * Real.pi ^ 2 * ν) ^ 3 * h1Sq u₀ ^ 2 < 2 * Real.pi ^ 2 * ν) :
    periodicTstar ν u₀ = ⊤ :=
  periodicTstar_eq_top_of_smallH1_of_rate hν (by positivity)
    (periodicEnstrophyRateBound_of_trilinear hK hT hM) hL hu₀ hmean hm hsmall

end PeriodicNSContinuation
