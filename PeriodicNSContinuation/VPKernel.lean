/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.DyadicBlock

/-!
# The de la Vallée Poussin kernel is `L¹`-bounded, uniformly in `R ≥ 2`

(step 3 toward `PeriodicLowFreqVorticityBound`). This uses the complex first-difference weight
`w_l(z) = 1 + R (e(z_l) − 1)`, for which `|w_l|² = 1 + 4R(R−1) sin²(π z_l)`. Because
`vpWeight` is a tensor product, `∏_l w_l · K` has coefficients `∏_i ψ(k_i)` with
`ψ = φ + R(φ(· − 1) − φ)` and `|ψ| ≤ 2`, since `φ` is `1/R`-Lipschitz. All names coined
(see README).
-/

noncomputable section
open MeasureTheory Set Real FeffermanClayNS NavierStokes3D TorusFourierNS

namespace PeriodicNSContinuation

/-- Coined. One-dimensional factor of `vpWeight`. -/
def vpφ (R : ℝ) (n : ℤ) : ℝ := min 1 (max 0 (2 - |(n : ℝ)| / R))

lemma vpWeight_eq_prod (R : ℝ) (k : Mode) : vpWeight R k = ∏ i, vpφ R (k i) := rfl

lemma vpφ_mem (R : ℝ) (n : ℤ) : 0 ≤ vpφ R n ∧ vpφ R n ≤ 1 :=
  ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

lemma vpφ_lip {R : ℝ} (hR : 0 < R) (n : ℤ) : |vpφ R (n - 1) - vpφ R n| ≤ 1 / R := by
  have key : ∀ u v : ℝ, |min 1 (max 0 u) - min 1 (max 0 v)| ≤ |u - v| := fun u v =>
    (abs_min_sub_min_le_max 1 (max 0 u) 1 (max 0 v)).trans (max_le (by simp)
      ((abs_max_sub_max_le_max 0 u 0 v).trans (max_le (by simp) le_rfl)))
  unfold vpφ
  refine (key _ _).trans ?_
  rw [show 2 - |((n - 1 : ℤ) : ℝ)| / R - (2 - |(n : ℝ)| / R) = (|(n : ℝ)| - |((n - 1 : ℤ) : ℝ)|) / R
    by ring, abs_div, abs_of_pos hR]
  apply div_le_div_of_nonneg_right _ hR.le
  refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
  push_cast; simp

/-- Coined. Tensor coefficient. -/
def tens (f g h : ℤ → ℂ) (k : Mode) : ℂ := f (k 0) * g (k 1) * h (k 2)

/-- Coined. First-difference operator in direction `l`: `(1 − a) c_k + a c_{k − e_l}`. -/
def fdOp (a : ℝ) (l : Fin 3) (c : Mode → ℂ) (k : Mode) : ℂ :=
  (1 - a) * c k + a * c (k - unitMode l)

/-- Coined. One-dimensional version of `fdOp`. -/
def fd1 (a : ℝ) (f : ℤ → ℂ) (n : ℤ) : ℂ := (1 - a) * f n + a * f (n - 1)

lemma fdOp_tens (a : ℝ) (f g h : ℤ → ℂ) :
    fdOp a 0 (tens f g h) = tens (fd1 a f) g h ∧ fdOp a 1 (tens f g h) = tens f (fd1 a g) h ∧
    fdOp a 2 (tens f g h) = tens f g (fd1 a h) := by
  refine ⟨?_, ?_, ?_⟩ <;> funext k <;> simp [fdOp, tens, fd1, unitMode] <;> ring

/-- Coined. Complex weight factor `1 + a (e(z_l) − 1)`. -/
def wFac (a : ℝ) (l : Fin 3) (z : Fin 3 → ℝ) : ℂ := 1 + a * (charE (unitMode l) z - 1)

lemma boxSupp_fdOp {N : ℕ} {c : Mode → ℂ} (hc : BoxSupp N c) (a : ℝ) (l : Fin 3) :
    BoxSupp (N + 1) (fdOp a l c) := by
  intro k hk
  have h1 := boxSupp_shift hc (unitMode l) (fun i => (abs_unitMode l i).1) k hk
  have h2 : c k = 0 := hc k fun h => hk (mem_modeBox.2 fun i =>
    (mem_modeBox.1 h i).trans (by push_cast; linarith))
  simp only at h1; simp [fdOp, h1, h2]

lemma wFac_mul_multKernel {N : ℕ} {c : Mode → ℂ} (hc : BoxSupp N c) (a : ℝ) (l : Fin 3)
    (z : Fin 3 → ℝ) :
    wFac a l z * multKernel (modeBox N) c z = multKernel (modeBox (N + 1)) (fdOp a l c) z := by
  have h1 := charE_mul_multKernel_box hc (unitMode l) (fun i => (abs_unitMode l i).1) z
  have h2 := multKernel_mono (Nat.le_succ N) hc z
  have e : wFac a l z * multKernel (modeBox N) c z =
      (1 - a) * multKernel (modeBox N) c z + a * (charE (unitMode l) z * multKernel (modeBox N) c z) := by
    unfold wFac; ring
  rw [e, h1, h2]
  simp only [multKernel, fdOp, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => by ring

lemma normSq_one_add_mul {e : ℂ} (he : ‖e‖ = 1) (a : ℝ) :
    ‖1 + (a : ℂ) * (e - 1)‖ ^ 2 = 1 + a * (a - 1) * ‖e - 1‖ ^ 2 := by
  have h : e.re ^ 2 + e.im ^ 2 = 1 := by
    have := congrArg (· ^ 2) he; simp only [Complex.sq_norm, Complex.normSq_apply, one_pow] at this
    linarith
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im]
  linear_combination a * h

lemma normSq_wFac (a : ℝ) (l : Fin 3) (z : Fin 3 → ℝ) :
    ‖wFac a l z‖ ^ 2 = 1 + 4 * (a * (a - 1)) * Real.sin (π * z l) ^ 2 := by
  rw [wFac, normSq_one_add_mul (norm_charE _ _), normSq_charE_unit_sub_one]; ring

lemma one_le_norm_wFac {a : ℝ} (ha : 1 ≤ a) (l : Fin 3) (z : Fin 3 → ℝ) : 1 ≤ ‖wFac a l z‖ := by
  have h := normSq_wFac a l z
  have : 1 ≤ ‖wFac a l z‖ ^ 2 := by
    rw [h]; have : 0 ≤ a * (a - 1) := mul_nonneg (by linarith) (by linarith); nlinarith [sq_nonneg (Real.sin (π * z l))]
  nlinarith [norm_nonneg (wFac a l z)]

lemma continuous_wFac (a : ℝ) (l : Fin 3) : Continuous (wFac a l) := by
  unfold wFac; have := continuous_charE (unitMode l); fun_prop

/-- **Proved.** `∫_{[0,1]³} ∏_l (1 + 4B sin²(π(x_l − y_l)))^{-2/3} dy ≤ 8 B^{-3/2}` for `B ≥ 1`. -/
theorem integral_prod_sinWeight_le {B : ℝ} (hB : 1 ≤ B) (x : Fin 3 → ℝ) :
    ∫ y in Icc (0 : Fin 3 → ℝ) 1, ∏ l, sinWeight B (x l - y l) ≤ 8 * B ^ (-(3 / 2 : ℝ)) := by
  have hB0 : 0 ≤ B := by linarith
  rw [volume_restrict_cell, integral_fintype_prod_eq_prod (f := fun l t => sinWeight B (x l - t))]
  have h1 : ∀ l : Fin 3, ∫ t in Icc (0 : ℝ) 1, sinWeight B (x l - t) ≤ 2 * B ^ (-(1 / 2 : ℝ)) := by
    intro l
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    exact integral_sinWeight_le hB (x l)
  have hn : ∀ l : Fin 3, 0 ≤ ∫ t in Icc (0 : ℝ) 1, sinWeight B (x l - t) := fun l =>
    setIntegral_nonneg measurableSet_Icc fun t _ => by unfold sinWeight; positivity
  rw [Fin.prod_univ_three]
  have hp : 0 ≤ B ^ (-(1 / 2 : ℝ)) := by positivity
  have e : 8 * B ^ (-(3 / 2 : ℝ)) = (2 * B ^ (-(1 / 2 : ℝ))) ^ 3 := by
    rw [mul_pow, ← rpow_natCast (B ^ _), ← rpow_mul hB0]; norm_num
  rw [e, pow_three, ← mul_assoc]
  exact mul_le_mul (mul_le_mul (h1 0) (h1 1) (hn 1) (by positivity)) (h1 2) (hn 2)
    (by positivity)

/-- Coined. Real product weight `∏_l |w_l(z)|`. -/
def fdWeight (a : ℝ) (z : Fin 3 → ℝ) : ℝ := ∏ l, ‖wFac a l z‖

lemma fdWeight_inv_sq_le {a : ℝ} (ha : 1 ≤ a) (z : Fin 3 → ℝ) :
    (fdWeight a z)⁻¹ ^ 2 ≤ ∏ l, sinWeight (a * (a - 1)) (z l) := by
  rw [fdWeight, ← Finset.prod_inv_distrib, ← Finset.prod_pow]
  refine Finset.prod_le_prod (fun l _ => by positivity) fun l _ => ?_
  have hb : 1 ≤ 1 + 4 * (a * (a - 1)) * Real.sin (π * z l) ^ 2 := by
    have : 0 ≤ a * (a - 1) := mul_nonneg (by linarith) (by linarith); nlinarith [sq_nonneg (Real.sin (π * z l))]
  rw [inv_pow, normSq_wFac, sinWeight, ← rpow_neg_one]
  exact rpow_le_rpow_of_exponent_le hb (by norm_num)

/-- **Proved.** Weighted bound: for `c` supported in the box of radius `N`, `a ≥ 1` and
`B = a(a − 1) ≥ 1`, `∫_y |K_c(x − y)| ≤ √(8 B^{-3/2}) · (Σ_{|k|∞ ≤ N+3} |d_k|²)^{1/2}`, where
`d = fdOp a 2 (fdOp a 1 (fdOp a 0 c))`. -/
theorem integral_norm_multKernel_fd_le {N : ℕ} {c : Mode → ℂ} (hc : BoxSupp N c) {a : ℝ}
    (ha : 1 ≤ a) (hB : 1 ≤ a * (a - 1)) (x : Fin 3 → ℝ) :
    ∫ y in Icc (0 : Fin 3 → ℝ) 1, ‖multKernel (modeBox N) c (x - y)‖ ≤
      Real.sqrt (8 * (a * (a - 1)) ^ (-(3 / 2 : ℝ))) *
        Real.sqrt (∑ k ∈ modeBox (N + 1 + 1 + 1),
          ‖fdOp a 2 (fdOp a 1 (fdOp a 0 c)) k‖ ^ 2) := by
  have hsub : Continuous fun y : Fin 3 → ℝ => x - y := continuous_const.sub continuous_id
  have hWc : Continuous (fdWeight a) :=
    continuous_finset_prod _ fun l _ => (continuous_wFac a l).norm
  have hW1 : ∀ z, 1 ≤ fdWeight a z := fun z => by
    rw [fdWeight, Fin.prod_univ_three]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_norm_wFac ha 0 z) (one_le_norm_wFac ha 1 z)) (one_le_norm_wFac ha 2 z)
  have h := cell_weighted_L1 (W := fun y => fdWeight a (x - y))
    (K := fun y => multKernel (modeBox N) c (x - y)) (hWc.comp hsub) (fun y => hW1 _)
    ((continuous_multKernel _ _).comp hsub)
  refine h.trans (mul_le_mul (Real.sqrt_le_sqrt ?_) (le_of_eq ?_) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _))
  · have hc' : Continuous fun y => (fdWeight a (x - y))⁻¹ ^ 2 :=
      ((hWc.comp hsub).inv₀ fun y => (zero_lt_one.trans_le (hW1 _)).ne').pow 2
    have hP : Continuous fun y : Fin 3 → ℝ => ∏ l, sinWeight (a * (a - 1)) (x l - y l) :=
      continuous_finset_prod _ fun l _ =>
        (continuous_sinWeight (by linarith)).comp (continuous_const.sub (continuous_apply l))
    refine (setIntegral_mono_on hc'.integrableOn_Icc hP.integrableOn_Icc measurableSet_Icc
      fun y _ => fdWeight_inv_sq_le ha (x - y)).trans ?_
    exact integral_prod_sinWeight_le hB x
  · congr 1
    have key : ∀ z, ‖((fdWeight a z : ℝ) : ℂ) * multKernel (modeBox N) c z‖ =
        ‖multKernel (modeBox (N + 1 + 1 + 1)) (fdOp a 2 (fdOp a 1 (fdOp a 0 c))) z‖ := by
      intro z
      have hc1 := boxSupp_fdOp hc a 0
      have hc2 := boxSupp_fdOp hc1 a 1
      rw [← wFac_mul_multKernel hc2, ← wFac_mul_multKernel hc1, ← wFac_mul_multKernel hc,
        norm_mul, Complex.norm_real, Real.norm_of_nonneg (by unfold fdWeight; positivity),
        fdWeight, Fin.prod_univ_three, norm_mul, norm_mul, norm_mul]
      ring
    simp_rw [key]
    exact integral_normSq_multKernel_sub _ _ x

lemma vpC_eq_tens (R : ℝ) :
    (fun k : Mode => ((vpWeight R k : ℝ) : ℂ)) =
      tens (fun n => (vpφ R n : ℂ)) (fun n => (vpφ R n : ℂ)) (fun n => (vpφ R n : ℂ)) := by
  funext k; simp [tens, vpWeight_eq_prod, Fin.prod_univ_three]

lemma boxSupp_vp {R : ℝ} (hR : 0 < R) :
    BoxSupp ⌈2 * R⌉₊ (fun k : Mode => ((vpWeight R k : ℝ) : ℂ)) := by
  intro k hk
  rw [mem_modeBox] at hk; push Not at hk
  obtain ⟨i, hi⟩ := hk
  have : 2 * R ≤ |(k i : ℝ)| := by
    have h1 : (⌈2 * R⌉₊ : ℝ) < |(k i : ℝ)| := by exact_mod_cast hi
    exact (Nat.le_ceil _).trans h1.le
  simp [vpWeight_eq_zero hR this]

lemma norm_fd1_vp_le {R : ℝ} (hR : 0 < R) (n : ℤ) : ‖fd1 R (fun n => (vpφ R n : ℂ)) n‖ ≤ 2 := by
  have e : fd1 R (fun n => (vpφ R n : ℂ)) n = ((vpφ R n + R * (vpφ R (n - 1) - vpφ R n) : ℝ) : ℂ) := by
    simp only [fd1]; push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  have h1 := vpφ_mem R n
  have h2 : |R * (vpφ R (n - 1) - vpφ R n)| ≤ 1 := by
    rw [abs_mul, abs_of_pos hR]
    calc R * _ ≤ R * (1 / R) := mul_le_mul_of_nonneg_left (vpφ_lip hR n) hR.le
      _ = 1 := by field_simp
  calc _ ≤ |vpφ R n| + |R * (vpφ R (n - 1) - vpφ R n)| := abs_add_le _ _
    _ ≤ 1 + 1 := add_le_add (by rw [abs_of_nonneg h1.1]; exact h1.2) h2
    _ = 2 := by norm_num

lemma rpow_aux {R : ℝ} (hR : 2 ≤ R) : (R * (R - 1)) ^ (-(3 / 2 : ℝ)) * R ^ 3 ≤ 4 := by
  have hR0 : 0 < R := by linarith
  have hB : 0 < R * (R - 1) := by nlinarith
  have e : R ^ 3 = (R ^ 2) ^ (3 / 2 : ℝ) := by
    rw [← rpow_natCast, ← rpow_natCast, ← rpow_mul hR0.le]; norm_num
  rw [e, rpow_neg hB.le, ← div_eq_inv_mul, ← div_rpow (by positivity) hB.le]
  have hq : R ^ 2 / (R * (R - 1)) ≤ 2 := by rw [div_le_iff₀ hB]; nlinarith
  calc (R ^ 2 / (R * (R - 1))) ^ (3 / 2 : ℝ) ≤ 2 ^ (3 / 2 : ℝ) :=
        rpow_le_rpow (by positivity) hq (by norm_num)
    _ ≤ 2 ^ (2 : ℝ) := rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 4 := by norm_num

/-- **Proved.** Step 3: the tensor de la Vallée Poussin kernel has `L¹(T³)` norm bounded
uniformly in `R ≥ 2` and in the translation `x`. -/
theorem exists_vp_L1_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 2 ≤ R → ∀ x : Fin 3 → ℝ,
    ∫ y in Icc (0 : Fin 3 → ℝ) 1,
      ‖multKernel (modeBox ⌈2 * R⌉₊) (fun k => ((vpWeight R k : ℝ) : ℂ)) (x - y)‖ ≤ C := by
  refine ⟨Real.sqrt (8 * 64 * 729 * 4), Real.sqrt_nonneg _, fun R hR x => ?_⟩
  have hR0 : 0 < R := by linarith
  have hB : 1 ≤ R * (R - 1) := by nlinarith
  refine (integral_norm_multKernel_fd_le (boxSupp_vp hR0) (by linarith) hB x).trans ?_
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  set N := ⌈2 * R⌉₊
  set φc : ℤ → ℂ := fun n => (vpφ R n : ℂ)
  have hd : fdOp R 2 (fdOp R 1 (fdOp R 0 (fun k => ((vpWeight R k : ℝ) : ℂ)))) =
      tens (fd1 R φc) (fd1 R φc) (fd1 R φc) := by
    rw [vpC_eq_tens, (fdOp_tens R _ _ _).1, (fdOp_tens R _ _ _).2.1, (fdOp_tens R _ _ _).2.2]
  rw [hd]
  have hpt : ∀ k, ‖tens (fd1 R φc) (fd1 R φc) (fd1 R φc) k‖ ^ 2 ≤ 64 := by
    intro k
    have h0 := norm_fd1_vp_le hR0 (k 0); have h1 := norm_fd1_vp_le hR0 (k 1)
    have h2 := norm_fd1_vp_le hR0 (k 2)
    rw [tens, norm_mul, norm_mul]
    have : ‖fd1 R φc (k 0)‖ * ‖fd1 R φc (k 1)‖ * ‖fd1 R φc (k 2)‖ ≤ 8 := by
      calc _ ≤ 2 * 2 * 2 := mul_le_mul (mul_le_mul h0 h1 (norm_nonneg _) (by norm_num)) h2
            (norm_nonneg _) (by norm_num)
        _ = 8 := by norm_num
    nlinarith [mul_nonneg (mul_nonneg (norm_nonneg (fd1 R φc (k 0))) (norm_nonneg (fd1 R φc (k 1))))
      (norm_nonneg (fd1 R φc (k 2)))]
  have hsum : ∑ k ∈ modeBox (N + 1 + 1 + 1), ‖tens (fd1 R φc) (fd1 R φc) (fd1 R φc) k‖ ^ 2 ≤
      64 * (729 * R ^ 3) := by
    refine (Finset.sum_le_sum fun k _ => hpt k).trans ?_
    rw [Finset.sum_const, card_modeBox, nsmul_eq_mul, mul_comm]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    have hN : (N : ℝ) ≤ 2 * R + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    push_cast
    calc (2 * ((N : ℝ) + 1 + 1 + 1) + 1) ^ 3 ≤ (9 * R) ^ 3 :=
          pow_le_pow_left₀ (by positivity) (by linarith) 3
      _ = 729 * R ^ 3 := by ring
  have hr := rpow_aux hR
  have hp : 0 ≤ (R * (R - 1)) ^ (-(3 / 2 : ℝ)) := by positivity
  calc 8 * (R * (R - 1)) ^ (-(3 / 2 : ℝ)) * ∑ k ∈ modeBox (N + 1 + 1 + 1), _
      ≤ 8 * (R * (R - 1)) ^ (-(3 / 2 : ℝ)) * (64 * (729 * R ^ 3)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 8 * 64 * 729 * ((R * (R - 1)) ^ (-(3 / 2 : ℝ)) * R ^ 3) := by ring
    _ ≤ 8 * 64 * 729 * 4 := mul_le_mul_of_nonneg_left hr (by norm_num)

end PeriodicNSContinuation
