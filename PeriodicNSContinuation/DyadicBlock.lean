/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.WeightIntegral

/-!
# Smooth dyadic blocks of `ξ_j ξ_b / |ξ|²` have uniformly `L¹`-bounded kernels

(step 2 toward `PeriodicLowFreqVorticityBound`). The block profile `blockF` is `C²` with compact
support, so its second differences at step `h` are `O(h²)`. Scaling by `2^s` then gives
`|c − 4^s Δc| ≲ 1`. All names coined (see README).
-/

noncomputable section
open MeasureTheory Set Real Filter Topology FeffermanClayNS NavierStokes3D TorusFourierNS

namespace PeriodicNSContinuation

/-- **Proved.** Second differences of a compactly supported `C²` function are `O(h²)`. -/
theorem exists_secondDiff_bound {F : (Fin 3 → ℝ) → ℝ} (hF : ContDiff ℝ 2 F)
    (hc : HasCompactSupport F) (v : Fin 3 → ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ p : Fin 3 → ℝ, ∀ h : ℝ,
      |F (p + h • v) - 2 * F p + F (p - h • v)| ≤ M * h ^ 2 := by
  set D1 : (Fin 3 → ℝ) → ℝ := fun q => fderiv ℝ F q v
  have hF1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hD1 : ContDiff ℝ 1 D1 := hF1.clm_apply contDiff_const
  set D2 : (Fin 3 → ℝ) → ℝ := fun q => fderiv ℝ D1 q v
  have hD2c : Continuous D2 := (hD1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hD1s : HasCompactSupport D1 := hc.fderiv_apply (𝕜 := ℝ) v
  have hD2s : HasCompactSupport D2 := hD1s.fderiv_apply (𝕜 := ℝ) v
  obtain ⟨M0, hM0⟩ := hD2c.bounded_above_of_compact_support hD2s
  refine ⟨max M0 0, le_max_right _ _, fun p h => ?_⟩
  set M := max M0 0
  have hline : ∀ q : Fin 3 → ℝ, ∀ t : ℝ, HasDerivAt (fun t : ℝ => q + t • v) v t := fun q t => by
    simpa using ((hasDerivAt_id t).smul_const v).const_add q
  have hφ : ∀ q t, HasDerivAt (fun t : ℝ => F (q + t • v)) (D1 (q + t • v)) t := fun q t =>
    ((hF.differentiable (by norm_num)) _).hasFDerivAt.comp_hasDerivAt t (hline q t)
  have hψ : ∀ q t, HasDerivAt (fun t : ℝ => D1 (q + t • v)) (D2 (q + t • v)) t := fun q t =>
    ((hD1.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt t (hline q t)
  have hlip : ∀ t, |D1 (p + t • v) - D1 (p + (t - h) • v)| ≤ M * |h| := by
    intro t
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := univ)
      (f := fun t => D1 (p + t • v)) (f' := fun t => D2 (p + t • v)) (C := M)
      (fun t _ => (hψ p t).hasDerivWithinAt) (fun t _ => (hM0 _).trans (le_max_left _ _))
      convex_univ (mem_univ (t - h)) (mem_univ t)
    simpa [Real.norm_eq_abs] using this
  have hg : ∀ t, HasDerivAt (fun t : ℝ => F (p + t • v) - F (p + (t - h) • v))
      (D1 (p + t • v) - D1 (p + (t - h) • v)) t := fun t =>
    (hφ p t).sub (HasDerivAt.comp_sub_const (f := fun t : ℝ => F (p + t • v)) t h (hφ p (t - h)))
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := univ) (C := M * |h|)
    (fun t _ => (hg t).hasDerivWithinAt) (fun t _ => by rw [Real.norm_eq_abs]; exact hlip t)
    convex_univ (mem_univ 0) (mem_univ h)
  simp only [Real.norm_eq_abs, sub_zero, zero_sub, sub_self, zero_smul, add_zero, neg_smul,
    ← sub_eq_add_neg] at this
  have e : F (p + h • v) - 2 * F p + F (p - h • v) = F (p + h • v) - F p - (F p - F (p - h • v)) := by
    ring
  rw [e, sq, ← abs_mul_abs_self h, ← mul_assoc]; exact this

/-- Coined. `|ξ|² = Σ ξ_i²`. -/
def sqn (ξ : Fin 3 → ℝ) : ℝ := ∑ i, ξ i ^ 2

/-- Coined. Smooth cutoff, `= 1` on `t ≤ 1` and `= 0` on `t ≥ 2`. -/
def cutχ (t : ℝ) : ℝ := Real.smoothTransition (2 - t)

/-- Coined. Dyadic block profile `(ξ_j ξ_b / |ξ|²)(χ(|ξ|²/4) − χ(|ξ|²))`. -/
def blockF (j b : Fin 3) (ξ : Fin 3 → ℝ) : ℝ :=
  ξ j * ξ b / sqn ξ * (cutχ (sqn ξ / 4) - cutχ (sqn ξ))

lemma cutχ_one {t : ℝ} (h : t ≤ 1) : cutχ t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma cutχ_zero {t : ℝ} (h : 2 ≤ t) : cutχ t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma cutχ_mem (t : ℝ) : 0 ≤ cutχ t ∧ cutχ t ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma contDiff_cutχ {n : ℕ∞} : ContDiff ℝ n cutχ :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

lemma contDiff_sqn {n : ℕ∞} : ContDiff ℝ n sqn :=
  ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).pow 2

lemma sqn_nonneg (ξ : Fin 3 → ℝ) : 0 ≤ sqn ξ := Finset.sum_nonneg fun i _ => sq_nonneg _

lemma sq_le_sqn (ξ : Fin 3 → ℝ) (i : Fin 3) : ξ i ^ 2 ≤ sqn ξ :=
  Finset.single_le_sum (f := fun i => ξ i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)

lemma blockF_eq_zero_of_ge {j b : Fin 3} {ξ : Fin 3 → ℝ} (h : 8 ≤ sqn ξ) : blockF j b ξ = 0 := by
  simp [blockF, cutχ_zero (by linarith : 2 ≤ sqn ξ / 4), cutχ_zero (by linarith : 2 ≤ sqn ξ)]

lemma blockF_eq_zero_of_le {j b : Fin 3} {ξ : Fin 3 → ℝ} (h : sqn ξ ≤ 1) : blockF j b ξ = 0 := by
  have h0 := sqn_nonneg ξ
  simp [blockF, cutχ_one (by linarith : sqn ξ / 4 ≤ 1), cutχ_one h]

lemma contDiff_blockF (j b : Fin 3) : ContDiff ℝ 2 (blockF j b) := by
  rw [contDiff_iff_contDiffAt]; intro ξ
  by_cases h : sqn ξ = 0
  · have hev : blockF j b =ᶠ[𝓝 ξ] fun _ => 0 := by
      have : ∀ᶠ η in 𝓝 ξ, sqn η < 1 :=
        (contDiff_sqn (n := 0)).continuous.continuousAt.eventually_lt continuousAt_const
          (by rw [h]; norm_num)
      filter_upwards [this] with η hη; exact blockF_eq_zero_of_le hη.le
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hs : ContDiff ℝ 2 sqn := contDiff_sqn
    exact ((((contDiff_apply ℝ ℝ j).mul (contDiff_apply ℝ ℝ b)).contDiffAt.div hs.contDiffAt h).mul
      ((contDiff_cutχ.comp (hs.div_const 4)).sub (contDiff_cutχ.comp hs)).contDiffAt)

lemma hasCompactSupport_blockF (j b : Fin 3) : HasCompactSupport (blockF j b) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin 3 → ℝ) 3) fun ξ hξ => ?_
  refine blockF_eq_zero_of_ge ?_
  by_contra hlt; push Not at hlt
  apply hξ
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  have := sq_le_sqn ξ i
  rw [Real.norm_eq_abs]
  exact abs_le.2 ⟨by nlinarith, by nlinarith⟩

lemma abs_blockF_le (j b : Fin 3) (ξ : Fin 3 → ℝ) : |blockF j b ξ| ≤ 1 := by
  have hq : |ξ j * ξ b / sqn ξ| ≤ 1 := by
    rcases eq_or_lt_of_le (sqn_nonneg ξ) with h | h
    · rw [← h]; simp
    rw [abs_div, abs_of_pos h, div_le_one h]
    have h1 := sq_le_sqn ξ j; have h2 := sq_le_sqn ξ b
    have : (ξ j * ξ b) ^ 2 ≤ sqn ξ ^ 2 := by
      rw [mul_pow]; exact mul_le_mul h1 h2 (sq_nonneg _) h.le |>.trans_eq (sq _).symm
    exact abs_le_of_sq_le_sq' this h.le |> fun h' => abs_le.2 h'
  have hc : |cutχ (sqn ξ / 4) - cutχ (sqn ξ)| ≤ 1 := by
    have := cutχ_mem (sqn ξ / 4); have := cutχ_mem (sqn ξ)
    rw [abs_le]; constructor <;> linarith
  rw [blockF, abs_mul]
  exact mul_le_one₀ hq (abs_nonneg _) hc

/-- Coined. Coefficients of the `s`-th dyadic block: `blockF j b (k / 2^s)`. -/
def blockC (j b : Fin 3) (s : ℕ) (k : Mode) : ℂ := (blockF j b (fun i => (k i : ℝ) / 2 ^ s) : ℂ)

lemma boxSupp_blockC (j b : Fin 3) (s : ℕ) : BoxSupp (3 * 2 ^ s) (blockC j b s) := by
  intro k hk
  rw [mem_modeBox] at hk; push Not at hk
  obtain ⟨i, hi⟩ := hk
  unfold blockC; rw [blockF_eq_zero_of_ge, Complex.ofReal_zero]
  have h2 : (0 : ℝ) < 2 ^ s := by positivity
  have hi' : (3 : ℝ) * 2 ^ s < |(k i : ℝ)| := by exact_mod_cast hi
  have : (3 : ℝ) < |(k i : ℝ) / 2 ^ s| := by
    rw [abs_div, abs_of_pos h2, lt_div_iff₀ h2]; exact hi'
  have hsq : (9 : ℝ) < ((k i : ℝ) / 2 ^ s) ^ 2 := by
    rw [← sq_abs]; nlinarith [abs_nonneg ((k i : ℝ) / 2 ^ s)]
  linarith [sq_le_sqn (fun i => (k i : ℝ) / 2 ^ s) i]

lemma scaled_shift (s : ℕ) (k : Mode) (l : Fin 3) :
    (fun i => ((k + unitMode l) i : ℝ) / 2 ^ s) =
        (fun i => (k i : ℝ) / 2 ^ s) + (1 / 2 ^ s : ℝ) • (Pi.single l 1 : Fin 3 → ℝ) ∧
    (fun i => ((k - unitMode l) i : ℝ) / 2 ^ s) =
        (fun i => (k i : ℝ) / 2 ^ s) - (1 / 2 ^ s : ℝ) • (Pi.single l 1 : Fin 3 → ℝ) := by
  constructor <;> funext i <;> by_cases h : i = l <;>
    simp [unitMode, h] <;> ring

/-- **Proved.** Uniform discrete Taylor bound `|c_k − 4^s Δc_k| ≤ 1 + Σ_l M_l` for the dyadic block. -/
theorem exists_blockC_coeff_bound (j b : Fin 3) :
    ∃ B, 0 ≤ B ∧ ∀ s : ℕ, ∀ k : Mode,
      ‖blockC j b s k - ((4 : ℝ) ^ s : ℝ) * secDiffSum (blockC j b s) k‖ ≤ B := by
  choose M hM0 hM using fun l : Fin 3 => exists_secondDiff_bound (contDiff_blockF j b)
    (hasCompactSupport_blockF j b) (Pi.single l 1)
  refine ⟨1 + ∑ l, M l, add_nonneg zero_le_one (Finset.sum_nonneg fun l _ => hM0 l), fun s k => ?_⟩
  set p : Fin 3 → ℝ := fun i => (k i : ℝ) / 2 ^ s
  set h : ℝ := 1 / 2 ^ s
  set F := blockF j b
  have he : blockC j b s k - ((4 : ℝ) ^ s : ℝ) * secDiffSum (blockC j b s) k =
      ((F p - (4 : ℝ) ^ s * ∑ l : Fin 3, (F (p + h • (Pi.single l 1 : Fin 3 → ℝ)) - 2 * F p +
        F (p - h • (Pi.single l 1 : Fin 3 → ℝ))) : ℝ) : ℂ) := by
    simp only [secDiffSum, blockC, fun l => (scaled_shift s k l).1, fun l => (scaled_shift s k l).2]
    push_cast; rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  have h4 : (4 : ℝ) ^ s * h ^ 2 = 1 := by
    simp only [h, div_pow, one_pow]
    rw [← pow_mul, mul_comm s 2, pow_mul]; norm_num
  have hsum : |(4 : ℝ) ^ s * ∑ l : Fin 3, (F (p + h • (Pi.single l 1 : Fin 3 → ℝ)) - 2 * F p +
      F (p - h • (Pi.single l 1 : Fin 3 → ℝ)))| ≤ ∑ l, M l := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc (4 : ℝ) ^ s * |∑ l : Fin 3, _| ≤ (4 : ℝ) ^ s * ∑ l : Fin 3, M l * h ^ 2 :=
          mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun l _ => hM l p h)) (by positivity)
      _ = ∑ l, M l := by rw [← Finset.sum_mul, mul_comm, mul_assoc, mul_comm (h ^ 2), h4, mul_one]
  have := abs_blockF_le j b p
  calc _ ≤ |F p| + |(4 : ℝ) ^ s * _| := abs_sub _ _
    _ ≤ _ := add_le_add this hsum

lemma rpow_four_pow (s : ℕ) : ((4 : ℝ) ^ s) ^ (-(3 / 2 : ℝ)) * 8 ^ s = 1 := by
  have h2 : (0 : ℝ) < 2 ^ s := by positivity
  have e4 : (4 : ℝ) ^ s = (2 ^ s) ^ (2 : ℝ) := by
    rw [Real.rpow_two, ← pow_mul, mul_comm, pow_mul]; norm_num
  have e8 : (8 : ℝ) ^ s = (2 ^ s) ^ (3 : ℝ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [e4, e8, ← Real.rpow_mul h2.le, ← Real.rpow_add h2]; norm_num

/-- **Proved.** Uniform `L¹` bound for the kernels of the smooth dyadic blocks of `ξ_jξ_b/|ξ|²`. -/
theorem exists_blockC_L1_bound (j b : Fin 3) :
    ∃ C, 0 ≤ C ∧ ∀ s : ℕ, ∀ x : Fin 3 → ℝ,
      ∫ y in Icc (0 : Fin 3 → ℝ) 1, ‖multKernel (modeBox (3 * 2 ^ s)) (blockC j b s) (x - y)‖ ≤ C := by
  obtain ⟨B, hB0, hB⟩ := exists_blockC_coeff_bound j b
  refine ⟨Real.sqrt (8 * 729 * B ^ 2), Real.sqrt_nonneg _, fun s x => ?_⟩
  have hA : (1 : ℝ) ≤ 4 ^ s := one_le_pow₀ (by norm_num)
  refine (integral_norm_multKernel_sub_le (boxSupp_blockC j b s) hA x).trans ?_
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  have hsum : ∑ k ∈ modeBox (3 * 2 ^ s + 1),
      ‖blockC j b s k - ((4 : ℝ) ^ s : ℝ) * secDiffSum (blockC j b s) k‖ ^ 2 ≤ 729 * 8 ^ s * B ^ 2 := by
    refine (Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hB s k) 2).trans ?_
    rw [Finset.sum_const, card_modeBox, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have h1 : (1 : ℝ) ≤ 2 ^ s := one_le_pow₀ (by norm_num)
    push_cast
    calc (2 * (3 * (2 : ℝ) ^ s + 1) + 1) ^ 3 ≤ (9 * 2 ^ s) ^ 3 :=
          pow_le_pow_left₀ (by positivity) (by linarith) 3
      _ = 729 * 8 ^ s := by rw [mul_pow, ← pow_mul, mul_comm s 3, pow_mul]; norm_num
  calc 8 * ((4 : ℝ) ^ s) ^ (-(3 / 2 : ℝ)) * ∑ k ∈ modeBox (3 * 2 ^ s + 1), _
      ≤ 8 * ((4 : ℝ) ^ s) ^ (-(3 / 2 : ℝ)) * (729 * 8 ^ s * B ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 8 * 729 * B ^ 2 * (((4 : ℝ) ^ s) ^ (-(3 / 2 : ℝ)) * 8 ^ s) := by ring
    _ = 8 * 729 * B ^ 2 := by rw [rpow_four_pow, mul_one]

/-- Coined. Real embedding of a mode. -/
def modeR (k : Mode) : Fin 3 → ℝ := fun i => (k i : ℝ)

lemma blockC_eq (j b : Fin 3) (s : ℕ) (k : Mode) :
    blockC j b s k = ((modeR k j * modeR k b / sqn (modeR k) *
      (cutχ (sqn (modeR k) / 4 ^ (s + 1)) - cutχ (sqn (modeR k) / 4 ^ s)) : ℝ) : ℂ) := by
  have h2 : (2 : ℝ) ^ s ≠ 0 := by positivity
  have hs : sqn (fun i => (k i : ℝ) / 2 ^ s) = sqn (modeR k) / 4 ^ s := by
    simp only [sqn, modeR, div_pow, ← Finset.sum_div]
    rw [← pow_mul, mul_comm s 2, pow_mul]; norm_num
  unfold blockC blockF; rw [hs]
  congr 1
  rcases eq_or_ne (sqn (modeR k)) 0 with h0 | h0
  · simp [h0]
  · have e : ((2 : ℝ) ^ s) ^ 2 = 4 ^ s := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    simp only [modeR, pow_succ]; field_simp; rw [e]; ring

/-- **Proved.** Telescoping: `Σ_{s<S}` blocks `= q(k)·(χ(|k|²/4^S) − χ(|k|²))`. -/
theorem sum_blockC (j b : Fin 3) (S : ℕ) (k : Mode) :
    ∑ s ∈ Finset.range S, blockC j b s k = ((modeR k j * modeR k b / sqn (modeR k) *
      (cutχ (sqn (modeR k) / 4 ^ S) - cutχ (sqn (modeR k))) : ℝ) : ℂ) := by
  simp only [blockC_eq, ← Complex.ofReal_sum, ← Finset.mul_sum]
  rw [Finset.sum_range_sub (fun s => cutχ (sqn (modeR k) / 4 ^ s))]; simp

end PeriodicNSContinuation
