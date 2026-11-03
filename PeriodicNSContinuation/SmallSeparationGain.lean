/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import Mathlib

/-!
# Small-separation gain for window drift (abstract)

`δ k` is the direction difference at window boundary `k` and `r k ≥ 0` is the pair separation.
Coined names (Nov 2026): `drift_le_lip_sum`, `SeparationSumDominated`, `holder_quotient_of_dominated`.

* `drift_le_lip_sum` (**proved**): per-window Lipschitz drift `‖δ(k+1) - δ k‖ ≤ L r k` gives
  `‖δ n - δ 0‖ ≤ L ∑_{k<n} r k`.
* `SeparationSumDominated r A` (**hypothesis**): `∑_{k<n} r k ≤ A r n` for all `n`. This holds, e.g., under geometric
  growth `r (k+1) ≥ ρ r k` with `ρ > 1`, where `A = 1/(ρ-1)`.
* `holder_quotient_of_dominated` (**proved**): suppose `‖δ 0‖ ≤ K₀ √(r 0)`, `r 0 ≤ r n` and `r n ≤ R`. Then
  `‖δ n‖ ≤ (K₀ + L A √R) √(r n)`. The bound is uniform in the window count `n`.

**Honest caveat.** The per-window constant `L` is in effect `sup |∇τ|` over a window of length `~1/‖ω‖∞`.
A uniform `L` is the gradient-of-direction control that part (A) / FDC is supposed to supply, so this file
reduces the window problem to (A). It does not remove the need for (A).
-/

open Finset

namespace PeriodicNSContinuation

variable {E : Type*} [NormedAddCommGroup E]

theorem drift_le_lip_sum (δ : ℕ → E) (r : ℕ → ℝ) {L : ℝ}
    (h : ∀ k, ‖δ (k + 1) - δ k‖ ≤ L * r k) (n : ℕ) :
    ‖δ n - δ 0‖ ≤ L * ∑ k ∈ range n, r k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add]
    calc ‖δ (n + 1) - δ 0‖ = ‖(δ (n + 1) - δ n) + (δ n - δ 0)‖ := by abel_nf
      _ ≤ ‖δ (n + 1) - δ n‖ + ‖δ n - δ 0‖ := norm_add_le _ _
      _ ≤ L * r n + L * ∑ k ∈ range n, r k := add_le_add (h n) ih
      _ = _ := by ring

/-- Hypothesis (coined): the separation history is dominated by its current value. -/
def SeparationSumDominated (r : ℕ → ℝ) (A : ℝ) : Prop :=
  ∀ n : ℕ, ∑ k ∈ range n, r k ≤ A * r n

theorem holder_quotient_of_dominated (δ : ℕ → E) (r : ℕ → ℝ) {L A K₀ R : ℝ}
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hK : 0 ≤ K₀)
    (h : ∀ k, ‖δ (k + 1) - δ k‖ ≤ L * r k) (hdom : SeparationSumDominated r A)
    (n : ℕ) (h0 : ‖δ 0‖ ≤ K₀ * Real.sqrt (r 0)) (hr0 : 0 ≤ r 0) (hmono : r 0 ≤ r n)
    (hR : r n ≤ R) :
    ‖δ n‖ ≤ (K₀ + L * A * Real.sqrt R) * Real.sqrt (r n) := by
  have hrn : 0 ≤ r n := hr0.trans hmono
  have hs : r n = Real.sqrt (r n) * Real.sqrt (r n) := (Real.mul_self_sqrt hrn).symm
  have hsq : Real.sqrt (r n) ≤ Real.sqrt R := Real.sqrt_le_sqrt hR
  have hd := drift_le_lip_sum δ r h n
  have h1 : L * ∑ k ∈ range n, r k ≤ L * A * Real.sqrt R * Real.sqrt (r n) := by
    calc L * ∑ k ∈ range n, r k ≤ L * (A * r n) := mul_le_mul_of_nonneg_left (hdom n) hL
      _ = L * A * Real.sqrt (r n) * Real.sqrt (r n) := by
          rw [mul_assoc (L * A), ← hs]; ring
      _ ≤ L * A * Real.sqrt R * Real.sqrt (r n) := by
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_left hsq (mul_nonneg hL hA)
  have h2 : K₀ * Real.sqrt (r 0) ≤ K₀ * Real.sqrt (r n) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmono) hK
  calc ‖δ n‖ = ‖(δ n - δ 0) + δ 0‖ := by abel_nf
    _ ≤ ‖δ n - δ 0‖ + ‖δ 0‖ := norm_add_le _ _
    _ ≤ _ := by nlinarith

end PeriodicNSContinuation
