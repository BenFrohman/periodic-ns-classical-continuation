/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.KernelWeighted

/-!
# The weight integral `∫ W_A⁻² ≲ A^{-3/2}`

The one-dimensional core is `integral_rpow_weight_le`.
-/

open MeasureTheory Set Real intervalIntegral FeffermanClayNS NavierStokes3D TorusFourierNS

namespace PeriodicNSContinuation

/-- **Proved.** One-dimensional core: for `b ≥ 16`,
`∫₀^{1/2} (1 + b t²)^{-2/3} dt ≤ 4 b^{-1/2}`. -/
theorem integral_rpow_weight_le {b : ℝ} (hb : 16 ≤ b) :
    ∫ t in (0 : ℝ)..(1 / 2), (1 + b * t ^ 2) ^ (-(2 / 3 : ℝ)) ≤ 4 * b ^ (-(1 / 2 : ℝ)) := by
  have hb0 : 0 < b := by linarith
  set t0 := b ^ (-(1 / 2 : ℝ)) with ht0
  have ht0pos : 0 < t0 := rpow_pos_of_pos hb0 _
  have ht0le : t0 ≤ 1 / 4 := by
    have : (16 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / 4 := by
      rw [show (16 : ℝ) = 4 ^ (2 : ℝ) by norm_num, ← rpow_mul (by norm_num)]; norm_num
    rw [← this]; exact rpow_le_rpow_of_nonpos (by norm_num) hb (by norm_num)
  have hcont : Continuous fun t : ℝ => (1 + b * t ^ 2) ^ (-(2 / 3 : ℝ)) :=
    Continuous.rpow_const (by fun_prop) fun t => Or.inl (by positivity)
  have hii : ∀ a c : ℝ, IntervalIntegrable (fun t : ℝ => (1 + b * t ^ 2) ^ (-(2 / 3 : ℝ))) volume a c :=
    fun a c => hcont.intervalIntegrable a c
  rw [← integral_add_adjacent_intervals (hii 0 t0) (hii t0 (1 / 2))]
  -- first piece
  have h1 : ∫ t in (0 : ℝ)..t0, (1 + b * t ^ 2) ^ (-(2 / 3 : ℝ)) ≤ t0 := by
    have := integral_mono_on (f := fun t : ℝ => (1 + b * t ^ 2) ^ (-(2 / 3 : ℝ)))
      (g := fun _ => (1 : ℝ)) ht0pos.le (hii 0 t0) (by simp) fun t _ =>
        rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg t]) (by norm_num)
    simpa using this
  -- second piece
  have hpow : ∀ t ∈ Icc t0 (1 / 2), (1 + b * t ^ 2) ^ (-(2 / 3 : ℝ)) ≤
      b ^ (-(2 / 3 : ℝ)) * t ^ (-(4 / 3 : ℝ)) := by
    intro t ht
    have htp : 0 < t := ht0pos.trans_le ht.1
    have e : b ^ (-(2 / 3 : ℝ)) * t ^ (-(4 / 3 : ℝ)) = (b * t ^ 2) ^ (-(2 / 3 : ℝ)) := by
      rw [mul_rpow hb0.le (by positivity), ← rpow_natCast, ← rpow_mul htp.le]; norm_num
    rw [e]; exact rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  have hnot : (0 : ℝ) ∉ uIcc t0 (1 / 2) := by
    rw [uIcc_of_le (by linarith)]; intro h; linarith [h.1]
  have h2 : ∫ t in t0..(1 / 2), (1 + b * t ^ 2) ^ (-(2 / 3 : ℝ)) ≤ 3 * b ^ (-(1 / 2 : ℝ)) := by
    have hint : IntervalIntegrable (fun t : ℝ => b ^ (-(2 / 3 : ℝ)) * t ^ (-(4 / 3 : ℝ)))
        volume t0 (1 / 2) :=
      (intervalIntegral.intervalIntegrable_rpow (Or.inr hnot)).const_mul _
    refine (integral_mono_on (by linarith) (hii _ _) hint hpow).trans ?_
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by norm_num, hnot⟩)]
    have hhalf : 0 ≤ (1 / 2 : ℝ) ^ (-(4 / 3 : ℝ) + 1) := by positivity
    have key : b ^ (-(2 / 3 : ℝ)) * t0 ^ (-(4 / 3 : ℝ) + 1) = b ^ (-(1 / 2 : ℝ)) := by
      rw [ht0, ← rpow_mul hb0.le, ← rpow_add hb0]; norm_num
    have hbp : 0 ≤ b ^ (-(2 / 3 : ℝ)) := by positivity
    have : ((1 / 2 : ℝ) ^ (-(4 / 3 : ℝ) + 1) - t0 ^ (-(4 / 3 : ℝ) + 1)) / (-(4 / 3 : ℝ) + 1) =
        3 * t0 ^ (-(4 / 3 : ℝ) + 1) - 3 * (1 / 2 : ℝ) ^ (-(4 / 3 : ℝ) + 1) := by
      norm_num; ring
    rw [this]; nlinarith [mul_nonneg hbp hhalf]
  linarith


/-- One-dimensional weight factor `(1 + 4A sin²(πu))^{-2/3}`. -/
noncomputable def sinWeight (A u : ℝ) : ℝ := (1 + 4 * A * Real.sin (π * u) ^ 2) ^ (-(2 / 3 : ℝ))

lemma continuous_sinWeight {A : ℝ} (hA : 0 ≤ A) : Continuous (sinWeight A) :=
  Continuous.rpow_const (by fun_prop) fun t => Or.inl (by positivity)

lemma sinWeight_periodic (A : ℝ) : Function.Periodic (sinWeight A) 1 := by
  intro u
  simp only [sinWeight, mul_add, mul_one, Real.sin_add_pi, neg_sq]

lemma sinWeight_neg (A u : ℝ) : sinWeight A (-u) = sinWeight A u := by
  simp only [sinWeight, mul_neg, Real.sin_neg, neg_sq]

lemma sinWeight_le {A u : ℝ} (hA : 0 ≤ A) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) :
    sinWeight A u ≤ (1 + 16 * A * u ^ 2) ^ (-(2 / 3 : ℝ)) := by
  have hs : 2 * u ≤ Real.sin (π * u) := by
    have := Real.mul_le_sin (x := π * u) (by positivity) (by nlinarith [Real.pi_pos])
    rwa [← mul_assoc, div_mul_cancel₀ _ Real.pi_ne_zero] at this
  refine rpow_le_rpow_of_nonpos (by positivity) ?_ (by norm_num)
  have : (2 * u) ^ 2 ≤ Real.sin (π * u) ^ 2 := pow_le_pow_left₀ (by linarith) hs 2
  nlinarith

/-- **Proved.** `∫₀¹ (1 + 4A sin²(π(x − y)))^{-2/3} dy ≤ 2 A^{-1/2}` for `A ≥ 1`, any `x`. -/
theorem integral_sinWeight_le {A : ℝ} (hA : 1 ≤ A) (x : ℝ) :
    ∫ y in (0 : ℝ)..1, sinWeight A (x - y) ≤ 2 * A ^ (-(1 / 2 : ℝ)) := by
  have hA0 : 0 ≤ A := by linarith
  have hc := continuous_sinWeight hA0
  rw [intervalIntegral.integral_comp_sub_left (sinWeight A) x, sub_zero]
  have hper := (sinWeight_periodic A).intervalIntegral_add_eq (x - 1) (-(1 / 2))
  rw [sub_add_cancel] at hper
  rw [hper, ← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable _ 0) (hc.intervalIntegrable 0 _)]
  have hneg : ∫ y in (-(1 / 2) : ℝ)..0, sinWeight A y = ∫ y in (0 : ℝ)..(1 / 2), sinWeight A y := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := 1 / 2) (sinWeight A)
    simp only [sinWeight_neg, neg_zero] at this; exact this.symm
  rw [hneg, show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num]
  have hhalf : ∫ y in (0 : ℝ)..(1 / 2), sinWeight A y ≤ A ^ (-(1 / 2 : ℝ)) := by
    have hcont : Continuous fun t : ℝ => (1 + 16 * A * t ^ 2) ^ (-(2 / 3 : ℝ)) :=
      Continuous.rpow_const (by fun_prop) fun t => Or.inl (by positivity)
    refine (intervalIntegral.integral_mono_on (by norm_num) (hc.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _) fun u hu => sinWeight_le hA0 hu.1 hu.2).trans ?_
    refine (integral_rpow_weight_le (b := 16 * A) (by linarith)).trans (le_of_eq ?_)
    rw [mul_rpow (by norm_num) hA0, show (16 : ℝ) = 4 ^ (2 : ℝ) by norm_num,
      ← rpow_mul (by norm_num)]
    norm_num; ring
  linarith

lemma normSq_charE_unit_sub_one (l : Fin 3) (z : Fin 3 → ℝ) :
    ‖charE (unitMode l) z - 1‖ ^ 2 = 4 * Real.sin (π * z l) ^ 2 := by
  have e : charE (unitMode l) z = Complex.exp (((2 * π * z l : ℝ) : ℂ) * Complex.I) := by
    rw [charE]; congr 1
    have : ∑ j, (((unitMode l j : ℤ) : ℝ) : ℂ) * (z j : ℂ) = (z l : ℂ) := by
      fin_cases l <;> simp [unitMode, Fin.sum_univ_three, Pi.single_apply]
    rw [this]; push_cast; ring
  rw [e, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.one_re, Complex.one_im, sub_zero]
  have h2 : 2 * π * z l = 2 * (π * z l) := by ring
  rw [h2, Real.cos_two_mul, Real.sin_two_mul]
  have := Real.sin_sq_add_cos_sq (π * z l)
  linear_combination (4 * Real.cos (π * z l) ^ 2 - 4) * this

/-- AM–GM: `W_A(z)⁻² ≤ ∏_l (1 + 4A sin²(π z_l))^{-2/3}`. -/
lemma cellWeight_inv_sq_le {A : ℝ} (hA : 0 ≤ A) (z : Fin 3 → ℝ) :
    (cellWeight A z)⁻¹ ^ 2 ≤ ∏ l, sinWeight A (z l) := by
  set a : Fin 3 → ℝ := fun l => 4 * A * Real.sin (π * z l) ^ 2
  have ha : ∀ l, 0 ≤ a l := fun l => by positivity
  have hW : cellWeight A z = 1 + (a 0 + a 1 + a 2) := by
    simp only [cellWeight, normSq_charE_unit_sub_one, Fin.sum_univ_three, a]; ring
  have hprod : ∏ l, sinWeight A (z l) = ((1 + a 0) * (1 + a 1) * (1 + a 2)) ^ (-(2 / 3 : ℝ)) := by
    simp only [Fin.prod_univ_three, sinWeight, a]
    rw [mul_rpow (by positivity) (by positivity), mul_rpow (by positivity) (by positivity)]
  rw [hprod, hW]
  have h0 := ha 0; have h1 := ha 1; have h2 := ha 2
  have hS : 0 < 1 + (a 0 + a 1 + a 2) := by linarith
  have hle : (1 + a 0) * (1 + a 1) * (1 + a 2) ≤ (1 + (a 0 + a 1 + a 2)) ^ (3 : ℕ) := by
    nlinarith [mul_nonneg h0 h1, mul_nonneg h1 h2, mul_nonneg h0 h2,
      mul_nonneg (mul_nonneg h0 h1) h2, sq_nonneg (a 0), sq_nonneg (a 1), sq_nonneg (a 2)]
  have e : (1 + (a 0 + a 1 + a 2))⁻¹ ^ 2 =
      ((1 + (a 0 + a 1 + a 2)) ^ (3 : ℕ)) ^ (-(2 / 3 : ℝ)) := by
    rw [← rpow_natCast _ 3, ← rpow_mul hS.le, inv_pow, ← rpow_natCast _ 2, ← rpow_neg hS.le]
    norm_num
  rw [e]
  exact rpow_le_rpow_of_nonpos (by positivity) hle (by norm_num)

/-- **Proved.** `∫_{[0,1]³} W_A(x − y)⁻² dy ≤ 8 A^{-3/2}` for `A ≥ 1`, uniformly in `x`. -/
theorem integral_cellWeight_inv_sq_le {A : ℝ} (hA : 1 ≤ A) (x : Fin 3 → ℝ) :
    ∫ y in Icc (0 : Fin 3 → ℝ) 1, (cellWeight A (x - y))⁻¹ ^ 2 ≤ 8 * A ^ (-(3 / 2 : ℝ)) := by
  have hA0 : 0 ≤ A := by linarith
  have hc := continuous_sinWeight hA0
  have hWc : Continuous fun y => (cellWeight A (x - y))⁻¹ ^ 2 :=
    (((continuous_cellWeight A).comp (continuous_const.sub continuous_id)).inv₀
      fun y => (zero_lt_one.trans_le (one_le_cellWeight hA0 (x - y))).ne').pow 2
  have hPc : Continuous fun y : Fin 3 → ℝ => ∏ l, sinWeight A (x l - y l) :=
    continuous_finset_prod _ fun l _ =>
      hc.comp (continuous_const.sub (continuous_apply l))
  refine (setIntegral_mono_on hWc.integrableOn_Icc hPc.integrableOn_Icc measurableSet_Icc
    fun y _ => cellWeight_inv_sq_le hA0 (x - y)).trans ?_
  rw [volume_restrict_cell, integral_fintype_prod_eq_prod (f := fun l t => sinWeight A (x l - t))]
  have h1 : ∀ l : Fin 3, ∫ t in Icc (0 : ℝ) 1, sinWeight A (x l - t) ≤ 2 * A ^ (-(1 / 2 : ℝ)) := by
    intro l
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    exact integral_sinWeight_le hA (x l)
  have hn : ∀ l : Fin 3, 0 ≤ ∫ t in Icc (0 : ℝ) 1, sinWeight A (x l - t) := fun l =>
    setIntegral_nonneg measurableSet_Icc fun t _ => by unfold sinWeight; positivity
  rw [Fin.prod_univ_three]
  have hp : 0 ≤ A ^ (-(1 / 2 : ℝ)) := by positivity
  have e : 8 * A ^ (-(3 / 2 : ℝ)) = (2 * A ^ (-(1 / 2 : ℝ))) ^ 3 := by
    rw [mul_pow, ← rpow_natCast (A ^ _), ← rpow_mul hA0]; norm_num
  rw [e, pow_three, ← mul_assoc]
  exact mul_le_mul (mul_le_mul (h1 0) (h1 1) (hn 1) (by positivity)) (h1 2) (hn 2)
    (by positivity)

/-- **Proved.** Block `L¹` bound: for `c` supported in the box of radius `N` and `A ≥ 1`,
`∫_y |K_c(x − y)| ≤ √(8 A^{-3/2}) · (Σ_{|k|∞ ≤ N+1} |c_k − A·Δc_k|²)^{1/2}`. -/
theorem integral_norm_multKernel_sub_le {N : ℕ} {c : Mode → ℂ} (hc : BoxSupp N c) {A : ℝ}
    (hA : 1 ≤ A) (x : Fin 3 → ℝ) :
    ∫ y in Icc (0 : Fin 3 → ℝ) 1, ‖multKernel (modeBox N) c (x - y)‖ ≤
      Real.sqrt (8 * A ^ (-(3 / 2 : ℝ))) *
        Real.sqrt (∑ k ∈ modeBox (N + 1), ‖c k - A * secDiffSum c k‖ ^ 2) := by
  have hA0 : 0 ≤ A := by linarith
  have hsub : Continuous fun y : Fin 3 → ℝ => x - y := continuous_const.sub continuous_id
  have h := cell_weighted_L1 (W := fun y => cellWeight A (x - y))
    (K := fun y => multKernel (modeBox N) c (x - y))
    ((continuous_cellWeight A).comp hsub) (fun y => one_le_cellWeight hA0 _)
    ((continuous_multKernel _ _).comp hsub)
  refine h.trans (mul_le_mul (Real.sqrt_le_sqrt (integral_cellWeight_inv_sq_le hA x))
    (le_of_eq ?_) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  congr 1
  simp_rw [cellWeight_mul_multKernel hc A]
  exact integral_normSq_multKernel_sub _ _ x

end PeriodicNSContinuation
