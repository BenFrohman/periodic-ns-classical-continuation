/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import Mathlib

/-!
# Exit from the high-vorticity set along a path (gap (iv)): Gronwall lower bound and two-threshold buffer

Along a particle path, `m(t) = |ω(X(t),t)|` satisfies `m' = α m + ν (Δω·τ)`, where `α = τ·Sτ` is the stretching rate.
If the total rate is bounded below, `m' ≥ -a m`, then `m(t) ≥ m(0) e^{-a t}`. So a path that starts in
`{m ≥ 2Λ}` stays in `{m ≥ Λ}` for `t ≤ log 2 / a`.

Coined names (Nov 2026): `lower_gronwall_exp`, `buffer_stay_time`.

**Exact gap.** The rate hypothesis is the whole difficulty. We need `a ≥ sup(-α) + ν sup |Δω·τ|/|ω|`
on the larger set. `|α| ≤ |S| ≲ ‖∇u‖∞` is a BKM-level quantity. (A) bounds only the orthogonal strain
`(I-τ⊗τ)Sτ`, not the longitudinal rate `α`. `ν|Δω|/|ω|` is not controlled by (A) either. A stay time of
`log 2 / a` is useful only if `a·T_* ≲ 1` on the relevant time scale, so no Prop is named (no drift).
-/

namespace PeriodicNSContinuation

/-- **Proved.** Gronwall lower bound: `m' ≥ -a m` implies `m t ≥ m 0 · exp (-a t)` for `t ≥ 0`. -/
theorem lower_gronwall_exp {m : ℝ → ℝ} (a : ℝ) (hd : Differentiable ℝ m)
    (hrate : ∀ t, -a * m t ≤ deriv m t) {t : ℝ} (ht : 0 ≤ t) :
    m 0 * Real.exp (-a * t) ≤ m t := by
  set h : ℝ → ℝ := fun s => m s * Real.exp (a * s) with hh
  have hdh : Differentiable ℝ h := hd.mul (Real.differentiable_exp.comp (differentiable_id.const_mul a))
  have hder : ∀ s, 0 ≤ deriv h s := by
    intro s
    have : HasDerivAt h (deriv m s * Real.exp (a * s) + m s * (Real.exp (a * s) * a)) s := by
      have h1 := (hd s).hasDerivAt
      have h2 : HasDerivAt (fun s => Real.exp (a * s)) (Real.exp (a * s) * a) s := by
        simpa using (Real.hasDerivAt_exp (a * s)).comp s ((hasDerivAt_id s).const_mul a)
      exact h1.mul h2
    rw [this.deriv]
    have he := Real.exp_pos (a * s)
    nlinarith [hrate s]
  have hmono : Monotone h := monotone_of_deriv_nonneg hdh hder
  have := hmono ht
  simp only [hh, mul_zero, Real.exp_zero, mul_one] at this
  have hpos := Real.exp_pos (-a * t)
  calc m 0 * Real.exp (-a * t) ≤ (m t * Real.exp (a * t)) * Real.exp (-a * t) :=
        mul_le_mul_of_nonneg_right this hpos.le
    _ = m t := by rw [mul_assoc, ← Real.exp_add]; ring_nf; simp

/-- **Proved.** Two-threshold buffer: starting in `{m ≥ 2Λ}` with `m' ≥ -a m` (`a > 0`), the path
stays in `{m ≥ Λ}` for all `0 ≤ t ≤ log 2 / a`. -/
theorem buffer_stay_time {m : ℝ → ℝ} {a Λ : ℝ} (ha : 0 < a) (hΛ : 0 ≤ Λ)
    (hd : Differentiable ℝ m) (hrate : ∀ t, -a * m t ≤ deriv m t)
    (h0 : 2 * Λ ≤ m 0) {t : ℝ} (ht : 0 ≤ t) (hT : t ≤ Real.log 2 / a) : Λ ≤ m t := by
  have hg := lower_gronwall_exp a hd hrate ht
  have hat : a * t ≤ Real.log 2 := by rw [le_div_iff₀ ha] at hT; linarith
  have hexp : (1/2 : ℝ) ≤ Real.exp (-a * t) := by
    have : Real.exp (-Real.log 2) ≤ Real.exp (-a * t) := Real.exp_le_exp.mpr (by linarith)
    rwa [Real.exp_neg, Real.exp_log (by norm_num), ← one_div] at this
  nlinarith [Real.exp_pos (-a * t)]

end PeriodicNSContinuation
