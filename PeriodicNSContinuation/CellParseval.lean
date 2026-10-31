/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.BiotSavartCoeff

/-!
# Orthogonality and Parseval for trigonometric polynomials on the unit cell
(foundations for step 2 toward `PeriodicLowFreqVorticityBound`). All names coined (see README).
-/

noncomputable section
open Set MeasureTheory FeffermanClayNS NavierStokes3D TorusFourierNS

namespace PeriodicNSContinuation

/-- **Proved.** `∫₀¹ e(n t) dt = [n = 0]`. -/
lemma integral_exp_int (n : ℤ) :
    ∫ t in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * t) =
      if n = 0 then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · have hc : (2 * Real.pi * Complex.I * (n : ℂ)) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero, h]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * Real.pi * Complex.I * (n : ℂ)) = 1 := by
      rw [Complex.exp_eq_one_iff]; exact ⟨n, by ring⟩
    simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero, h1,
      sub_self, zero_div]

lemma charE_eq_prod (k : Mode) (x : Fin 3 → ℝ) :
    charE k x = ∏ j, Complex.exp (2 * Real.pi * Complex.I * ((k j : ℤ) : ℂ) * (x j : ℂ)) := by
  rw [charE, Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  push_cast; ring_nf

lemma volume_restrict_cell :
    (volume : Measure (Fin 3 → ℝ)).restrict (Icc 0 1) =
      Measure.pi fun _ => (volume : Measure ℝ).restrict (Icc 0 1) := by
  rw [← Set.pi_univ_Icc, volume_pi, Measure.restrict_pi_pi]; rfl

/-- **Proved.** `∫_{[0,1]³} e(k·x) dx = [k = 0]`. -/
lemma integral_charE (k : Mode) :
    ∫ x in Icc (0 : Fin 3 → ℝ) 1, charE k x = if k = 0 then 1 else 0 := by
  simp_rw [charE_eq_prod]
  rw [volume_restrict_cell]
  refine (integral_fintype_prod_eq_prod (E := fun _ => ℝ)
    (μ := fun _ => (volume : Measure ℝ).restrict (Icc 0 1))
    (fun j (t : ℝ) => Complex.exp (2 * Real.pi * Complex.I * ((k j : ℤ) : ℂ) * (t : ℂ)))).trans ?_
  have e1 : ∀ j, ∫ t in Icc (0 : ℝ) 1,
      Complex.exp (2 * Real.pi * Complex.I * ((k j : ℤ) : ℂ) * (t : ℂ)) =
        if k j = 0 then 1 else 0 := fun j => by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    exact integral_exp_int (k j)
  refine (Finset.prod_congr rfl fun j _ => e1 j).trans ?_
  by_cases hk : k = 0
  · subst hk; simp
  · rw [if_neg hk]
    obtain ⟨j, hj⟩ : ∃ j, k j ≠ 0 := by
      by_contra h; push Not at h; exact hk (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

lemma charE_mul_conj (k l : Mode) (x : Fin 3 → ℝ) :
    charE k x * (starRingEnd ℂ) (charE l x) = charE (k - l) x := by
  simp only [charE, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, map_sum, Complex.conj_ofReal, Complex.conj_I, map_ofNat, Pi.sub_apply,
    Int.cast_sub, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib]
  ring

/-- **Proved.** Orthogonality: `∫ e_k \bar e_l = [k = l]`. -/
lemma integral_charE_mul_conj (k l : Mode) :
    ∫ x in Icc (0 : Fin 3 → ℝ) 1, charE k x * (starRingEnd ℂ) (charE l x) =
      if k = l then 1 else 0 := by
  simp_rw [charE_mul_conj, integral_charE, sub_eq_zero]

/-- **Proved.** Parseval for trigonometric polynomials on the cell:
`∫ |Σ_{k∈S} c_k e_k|² = Σ_{k∈S} |c_k|²`. -/
theorem integral_normSq_multKernel (S : Finset Mode) (c : Mode → ℂ) :
    ∫ x in Icc (0 : Fin 3 → ℝ) 1, ‖multKernel S c x‖ ^ 2 = ∑ k ∈ S, ‖c k‖ ^ 2 := by
  have h : ∀ x, ((‖multKernel S c x‖ ^ 2 : ℝ) : ℂ) =
      ∑ k ∈ S, ∑ l ∈ S, c k * (starRingEnd ℂ) (c l) *
        (charE k x * (starRingEnd ℂ) (charE l x)) := by
    intro x
    rw [Complex.ofReal_pow, ← Complex.mul_conj', multKernel, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul]; ring
  suffices key : ∫ x in Icc (0 : Fin 3 → ℝ) 1, ((‖multKernel S c x‖ ^ 2 : ℝ) : ℂ) =
      ((∑ k ∈ S, ‖c k‖ ^ 2 : ℝ) : ℂ) by
    have e := _root_.integral_complex_ofReal (μ := volume.restrict (Icc (0 : Fin 3 → ℝ) 1))
      (f := fun x => ‖multKernel S c x‖ ^ 2)
    exact_mod_cast e.symm.trans key
  simp_rw [h]
  have hint : ∀ k l, Integrable (fun x => c k * (starRingEnd ℂ) (c l) *
      (charE k x * (starRingEnd ℂ) (charE l x))) (volume.restrict (Icc (0 : Fin 3 → ℝ) 1)) :=
    fun k l => (continuous_const.mul ((continuous_charE k).mul
      (Complex.continuous_conj.comp (continuous_charE l)))).integrableOn_Icc
  rw [integral_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ => hint k l]
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [integral_finset_sum _ fun l _ => hint _ l]
  refine (Finset.sum_congr rfl fun l _ => (MeasureTheory.integral_const_mul _ _).trans
    (congrArg _ (integral_charE_mul_conj k l))).trans ?_
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq, if_pos hk, Complex.mul_conj']
