/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import Mathlib

/-!
# Drift across consecutive buffer windows: abstract cancellation lemmas

Let `d k` be the change of the two-point direction difference `δτ = τ(x) - τ(y)` over window `k`.
There are about `n ≈ ∫ ‖ω‖∞ dt` windows.

Coined names (Nov 2026): `window_drift_linear`, `window_drift_sq_eq_corr`,
`window_drift_sqrt_of_orthogonal`, `window_drift_sqrt_of_corr`, `WindowCorrelationSum`.

* `window_drift_linear` — **proved**: `‖∑ d‖ ≤ n B`. This is the no-cancellation (BKM-type) count.
* `window_drift_sq_eq_corr` — **proved**: `‖∑ d‖² = ∑_{j,k} ⟨d j, d k⟩`.
* `window_drift_sqrt_of_corr` — **proved**: if the correlation sum is at most `C n`
  (`WindowCorrelationSum C`), then `‖∑ d‖ ≤ √(C n)`. This is random-walk growth.
* `window_drift_sqrt_of_orthogonal` — **proved**: pairwise orthogonal increments bounded by `B` give `‖∑ d‖ ≤ B √n`.

`WindowCorrelationSum` is a hypothesis about an abstract sequence. It is not a statement about Navier–Stokes.
**Honest caveat.** `√n ≈ (∫‖ω‖∞)^{1/2}` is still unbounded as `∫‖ω‖∞ → ∞`, so √n cancellation alone does
not avoid BKM. Line-field (B) needs `|δτ| ≤ K |x-y|^{1/2}` with `K` independent of `n`. That requires a
correlation sum `O(1)` (summable correlations of a *mean-zero* sequence), or a gain from small
`|x-y|`. Note that `∑ d` telescopes, so `|∑ d| ≤ 2` trivially; the content lies entirely in the
`|x-y|^{1/2}` normalisation.
-/

open scoped RealInnerProductSpace
open Finset

namespace PeriodicNSContinuation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem window_drift_linear (d : ℕ → E) {B : ℝ} (hB : ∀ k, ‖d k‖ ≤ B) (n : ℕ) :
    ‖∑ k ∈ range n, d k‖ ≤ n * B := by
  calc ‖∑ k ∈ range n, d k‖ ≤ ∑ k ∈ range n, ‖d k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ range n, B := sum_le_sum fun k _ => hB k
    _ = n * B := by simp

theorem window_drift_sq_eq_corr (d : ℕ → E) (n : ℕ) :
    ‖∑ k ∈ range n, d k‖ ^ 2 = ∑ j ∈ range n, ∑ k ∈ range n, ⟪d j, d k⟫ := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp_rw [inner_sum]

/-- Hypothesis (coined): the window-increment correlation sum grows at most linearly. -/
def WindowCorrelationSum (d : ℕ → E) (C : ℝ) : Prop :=
  ∀ n : ℕ, ∑ j ∈ range n, ∑ k ∈ range n, ⟪d j, d k⟫ ≤ C * n

theorem window_drift_sqrt_of_corr (d : ℕ → E) {C : ℝ} (h : WindowCorrelationSum d C) (n : ℕ) :
    ‖∑ k ∈ range n, d k‖ ≤ Real.sqrt (C * n) := by
  apply Real.le_sqrt_of_sq_le
  rw [window_drift_sq_eq_corr]; exact h n

theorem window_drift_sqrt_of_orthogonal (d : ℕ → E) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ k, ‖d k‖ ≤ B)
    (horth : ∀ j k, j ≠ k → ⟪d j, d k⟫ = 0) (n : ℕ) :
    ‖∑ k ∈ range n, d k‖ ≤ B * Real.sqrt n := by
  have hcorr : WindowCorrelationSum d (B ^ 2) := by
    intro n
    have : ∀ j ∈ range n, ∑ k ∈ range n, ⟪d j, d k⟫ = ‖d j‖ ^ 2 := by
      intro j hj
      rw [sum_eq_single j (fun k _ hk => horth j k (Ne.symm hk)) (fun h => absurd hj h),
        real_inner_self_eq_norm_sq]
    rw [sum_congr rfl this]
    calc ∑ j ∈ range n, ‖d j‖ ^ 2 ≤ ∑ _j ∈ range n, B ^ 2 :=
          sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hB j) 2
      _ = B ^ 2 * n := by simp [mul_comm]
  calc ‖∑ k ∈ range n, d k‖ ≤ Real.sqrt (B ^ 2 * n) := window_drift_sqrt_of_corr d hcorr n
    _ = B * Real.sqrt n := by rw [Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB0]

end PeriodicNSContinuation
