/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.LineField

/-!
# The viscous term in `Dτ/Dt`: pointwise structure (attack on step 1 toward (A) ⇒ B_line)

Write `ω = m τ` with `m = |ω|` and `|τ| = 1`. Then
`Δω = m Δτ + 2 (∇m·∇)τ + (Δm) τ`, and the viscous part of `Dτ/Dt` is
`ν (I-τ⊗τ)Δω / m = ν [ (I-τ⊗τ)Δτ + 2 (∇ log m · ∇) τ ]`. The term `(∇ log m · ∇) τ` is already
perpendicular to `τ`. For unit `τ`, `(I-τ⊗τ)Δτ = Δτ + |∇τ|² τ`, which is the harmonic-map heat-flow structure.

Coined names (November 2026): `perpPart_smul_self`, `viscous_projection_decomposition`,
`perpPart_of_inner_neg`, `inner_fderiv_of_unit`.

* `perpPart_smul_self` — **proved**: the projection kills `(Δm) τ`.
* `viscous_projection_decomposition` — **proved**: the algebraic form of the decomposition above,
  with the jets `L = Δτ`, `D = (∇m·∇)τ` and `c = Δm` given as vectors.
* `inner_fderiv_of_unit` — **proved** (calculus): for a differentiable unit field, `⟨τ, ∂_v τ⟩ = 0`,
  so `perpPart τ (∂_v τ) = ∂_v τ`.
* `perpPart_of_inner_neg` — **proved**: if `⟨τ, L⟩ = -g`, for example `g = |∇τ|²` from differentiating
  `⟨τ,∂τ⟩ = 0` once more, then `(I-τ⊗τ)L = L + g τ`.

**What these identities do not give (on paper; see `paper/route_B_scoping.md`).**
(a) There is no maximum principle with a good sign. The target `S²` (or `RP²` for the line field) has
positive curvature, and Bochner gives `(∂ₜ-Δ)|∇τ|² ≤ -2|∇²τ|² + C|∇τ|⁴`. The quartic term has the bad sign,
and harmonic-map heat flow into spheres can blow up (Coron–Ghidaglia, Chang–Ding–Ye).
(b) The drift `2ν(∇ log m·∇)τ` has coefficient `|∇ log |ω||`, and nothing bounds it on the high set.
Under Navier–Stokes scaling it is of order `‖ω‖∞^{1/2}`.
(c) The `τ` equation is not closed: bending, `m` and the drift are all coupled back through Biot–Savart.
No named Prop is added for (b). A uniform bound on `|∇ log |ω||` over the high set is not weaker than
the direction regularity it would serve (no drift).
-/

open scoped RealInnerProductSpace

namespace PeriodicNSContinuation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem perpPart_smul_self {t : E} (ht : ‖t‖ = 1) (c : ℝ) : perpPart t (c • t) = 0 := by
  simp [perpPart, inner_smul_right, real_inner_self_eq_norm_sq, ht]

/-- **Proved.** `(I-τ⊗τ)(mL + 2D + cτ)/m = (I-τ⊗τ)L + (2/m)(I-τ⊗τ)D`. -/
theorem viscous_projection_decomposition {t : E} (ht : ‖t‖ = 1) {m : ℝ} (hm : m ≠ 0)
    (L D : E) (c : ℝ) :
    m⁻¹ • perpPart t (m • L + (2:ℝ) • D + c • t) =
      perpPart t L + (2 / m) • perpPart t D := by
  rw [perpPart_add, perpPart_add, perpPart_smul_self ht, add_zero, perpPart_smul, perpPart_smul,
    smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hm, one_smul, div_eq_inv_mul, mul_comm]

/-- **Proved.** Harmonic-map form: if `⟨τ, L⟩ = -g` then `(I-τ⊗τ)L = L + gτ`. -/
theorem perpPart_of_inner_neg {t L : E} {g : ℝ} (h : ⟪t, L⟫ = -g) :
    perpPart t L = L + g • t := by
  simp [perpPart, h, sub_eq_add_neg]

/-- **Proved.** For a differentiable unit field, `⟨τ, ∂ᵥτ⟩ = 0`. -/
theorem inner_fderiv_of_unit {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {τ : F → E} (hd : Differentiable ℝ τ) (hu : ∀ y, ‖τ y‖ = 1) (x v : F) :
    ⟪τ x, fderiv ℝ τ x v⟫ = 0 := by
  have hconst : (fun y => ⟪τ y, τ y⟫) = fun _ => (1:ℝ) := by
    funext y; rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have h := ((hd x).hasFDerivAt.inner ℝ (hd x).hasFDerivAt)
  rw [hconst] at h
  have h0 := h.unique (hasFDerivAt_const (1:ℝ) x)
  have := congrArg (fun f => f v) h0
  simp only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, fderivInnerCLM_apply] at this
  rw [real_inner_comm] at this; rw [real_inner_comm]
  linarith

/-- **Proved.** Hence the first-order direction derivatives are already perpendicular. -/
theorem perpPart_fderiv_of_unit {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {τ : F → E} (hd : Differentiable ℝ τ) (hu : ∀ y, ‖τ y‖ = 1) (x v : F) :
    perpPart (τ x) (fderiv ℝ τ x v) = fderiv ℝ τ x v := by
  simp [perpPart, inner_fderiv_of_unit hd hu x v]

end PeriodicNSContinuation
