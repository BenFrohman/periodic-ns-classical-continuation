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

end PeriodicNSContinuation
