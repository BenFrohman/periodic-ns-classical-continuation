/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.HighSetExit
import PeriodicNSContinuation.ViscousDirection

/-!
# The scale-critical product `a · T_*` (gap (iv))

Coined names (Nov 2026): `rescalePath`, `rescalePath_rate`, `buffer_stay_time_ratio`, `inner_viscous_along`.

* `rescalePath_rate` — **proved**: under the NS scaling `m_λ(t) = λ² m(λ² t)`, a rate bound `m' ≥ -a m`
  becomes `m_λ' ≥ -(λ² a) m_λ`, while the threshold `Λ` becomes `λ² Λ`. So `a/Λ`, and hence
  `(log 2 / a)·Λ`, is scale invariant. No choice of scale can make it small: it has to be an absolute constant.
* `buffer_stay_time_ratio` — **proved**: if `a ≤ c Λ`, then the stay time is at least `log 2 / (c Λ)`.
* `inner_viscous_along` — **proved** (algebra): for `ω = m τ` with a unit `τ`,
  `⟨τ, Δω⟩ = Δm - m |∇τ|²` (with jets `L = Δτ`, `⟨τ,L⟫ = -|∇τ|²`, `⟨τ,D⟫ = 0`).
  At a spatial maximum of `m`, `Δm ≤ 0`, so the viscous part of `m'/m` is `≤ -|∇τ|² ≤ 0` there:
  viscosity always pushes the peak **down**. Any absolute constant has to come from the stretching term.

**Open (not named, per the no-drift rule).** An absolute `c` with
`sup_{|ω| ≥ θ‖ω‖∞} (-α - ν Δω·τ/|ω|) ≤ c ‖ω‖∞`. Here `α = τ·Sτ`, and the pointwise bound `|S| ≤ C|ω|`
fails for nonlocal strain (Biot–Savart). Only `‖S‖∞ ≤ C ‖ω‖∞ (1 + log⁺(‖ω‖_{C^s}/‖ω‖∞))` is known
(Beale–Kato–Majda). Even an absolute `c` would give a stay window of only `log 2/(c‖ω‖∞)`, which is one
critical time. Summed over the windows that would also need (A)-controlled direction drift
(`twoPoint_direction_drift`: rate `2B`), it reproduces `∫‖ω‖∞`, the BKM integral.
-/

open scoped RealInnerProductSpace

namespace PeriodicNSContinuation

/-- NS parabolic rescaling of a path magnitude. -/
noncomputable def rescalePath (lam : ℝ) (m : ℝ → ℝ) : ℝ → ℝ := fun t => lam ^ 2 * m (lam ^ 2 * t)

theorem rescalePath_rate {m : ℝ → ℝ} {a lam : ℝ} (hd : Differentiable ℝ m)
    (hrate : ∀ t, -a * m t ≤ deriv m t) (t : ℝ) :
    -(lam ^ 2 * a) * rescalePath lam m t ≤ deriv (rescalePath lam m) t := by
  have h : HasDerivAt (rescalePath lam m) (lam ^ 2 * (deriv m (lam ^ 2 * t) * lam ^ 2)) t := by
    have := (hd (lam ^ 2 * t)).hasDerivAt.comp t ((hasDerivAt_id t).const_mul (lam ^ 2))
    simpa [rescalePath] using this.const_mul (lam ^ 2)
  rw [h.deriv]
  have hl : 0 ≤ lam ^ 2 * lam ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left (hrate (lam ^ 2 * t)) hl
  simp only [rescalePath]; nlinarith

theorem rescalePath_differentiable {m : ℝ → ℝ} (lam : ℝ) (hd : Differentiable ℝ m) :
    Differentiable ℝ (rescalePath lam m) :=
  (hd.comp (differentiable_id.const_mul _)).const_mul _

/-- **Proved.** The stay time with a rate-to-threshold ratio `c`. -/
theorem buffer_stay_time_ratio {m : ℝ → ℝ} {c Λ : ℝ} (hc : 0 < c) (hΛ : 0 < Λ)
    (hd : Differentiable ℝ m) (hrate : ∀ t, -(c * Λ) * m t ≤ deriv m t)
    (h0 : 2 * Λ ≤ m 0) {t : ℝ} (ht : 0 ≤ t) (hT : t ≤ Real.log 2 / (c * Λ)) : Λ ≤ m t :=
  buffer_stay_time (mul_pos hc hΛ) hΛ.le hd hrate h0 ht hT

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Proved.** `⟨τ, mL + 2D + cτ⟩ = c - m g` when `‖τ‖ = 1`, `⟨τ,L⟩ = -g`, `⟨τ,D⟩ = 0`. -/
theorem inner_viscous_along {t L D : E} (ht : ‖t‖ = 1) {m g c : ℝ} (hL : ⟪t, L⟫ = -g)
    (hD : ⟪t, D⟫ = 0) : ⟪t, m • L + (2:ℝ) • D + c • t⟫ = c - m * g := by
  simp only [inner_add_right, inner_smul_right, hL, hD, real_inner_self_eq_norm_sq, ht]; ring

end PeriodicNSContinuation
