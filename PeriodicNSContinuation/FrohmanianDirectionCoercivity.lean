/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.BendingRate

/-!
# Frohmanian Direction Coercivity (coined November 2026; **OPEN**)

`FrohmanianDirectionCoercivity` is a **coined name** (November 2026). It is the scale-invariant
form of Frohmanian Tether Hypothesis (A): on the high-vorticity set the bending strain
`|(I-τ⊗τ)Sτ|` is `o(|ω|)`. For every `ε > 0` there is a threshold `Λ_ε` with
`|bend| ≤ ε |ω|` wherever `|ω| ≥ Λ_ε`.

Why this form. The two-point candidate
`δξ·(Sξ(x)-Sξ(y)) ≤ -γ|δξ|² + ε(|∇ξ(x)|²+|∇ξ(y)|²) + K_ε|δξ|²` is degenerate, because `γ` and
`K_ε` merge into one Lipschitz bound on `Sξ`. Here both sides scale like `|ω|`
(under `u ↦ λu(λ·)` the ratio `|bend|/|ω|` is invariant), so the statement is critical. It is not
a bound uniform in `‖ω‖∞`.

* `frohmanianDirectionCoercivity_of_A` — **proved**: (A) implies this Prop.
* Converse, and whether this Prop alone gives `VortDirHolderHalf`: **open target, not a theorem.**

The metric tether `B_F` does not enter: it is not a term of plain Navier–Stokes. Added to the
vorticity equation with `F` = enstrophy, it contributes `κ|ω| c (I-τ⊗τ)u` to `Dτ/Dt`, where
`c = ⟨u,ω⟩/⟨u,u⟩`. That term is sign-indefinite against the bending and is not a `-γ|bend|²`
damping. See `README` / the numerical log.
-/

open Set Filter Topology MeasureTheory InnerProductSpace FeffermanClayNS NavierStokes3D
open scoped RealInnerProductSpace

namespace PeriodicNSContinuation
open Corrected

/-- Coined (November 2026). On `[0,T)`, bending strain is `o(|ω|)` on the high set. -/
def OrthogonalStrainSublinear (u : TimeDependentVelocity) (T : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ Λ : ℝ, 0 < Λ ∧ ∀ t ∈ Ico (0:ℝ) T, ∀ x : T3,
    Λ ≤ ‖vorticity (u t) x‖ → ‖orthogonalStrain (u t) x‖ ≤ ε * ‖vorticity (u t) x‖

/-- Coined (November 2026). **OPEN.** Frohmanian Direction Coercivity. -/
def FrohmanianDirectionCoercivity (ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure), IsPeriodicMaximalSolution ν u₀ u p →
      ∀ T : ℝ, periodicTstar ν u₀ = (T : EReal) → OrthogonalStrainSublinear u T

theorem orthogonalStrainSublinear_of_bounded {u : TimeDependentVelocity} {T : ℝ}
    (h : OrthogonalStrainBounded u T) : OrthogonalStrainSublinear u T := by
  obtain ⟨Λ, C, hΛ, hC⟩ := h
  unfold OrthogonalStrainSublinear
  intro ε hε
  refine ⟨max Λ (|C| / ε + 1), lt_of_lt_of_le hΛ (le_max_left _ _), fun t ht x hx => ?_⟩
  have h1 : Λ ≤ ‖vorticity (u t) x‖ := le_trans (le_max_left _ _) hx
  have h2 : |C| / ε + 1 ≤ ‖vorticity (u t) x‖ := le_trans (le_max_right _ _) hx
  have h3 : |C| ≤ ε * ‖vorticity (u t) x‖ := by
    have := (div_le_iff₀ hε).1 (by linarith : |C| / ε ≤ ‖vorticity (u t) x‖)
    linarith
  exact le_trans (hC t ht x h1) (le_trans (le_abs_self C) h3)

/-- **Proved.** Frohmanian Tether Hypothesis (A) implies Frohmanian Direction Coercivity. -/
theorem frohmanianDirectionCoercivity_of_A {ν : ℝ} (h : PeriodicOrthogonalStrainControl ν) :
    FrohmanianDirectionCoercivity ν :=
  fun hν u₀ hu₀ u p hm T hT => orthogonalStrainSublinear_of_bounded (h hν u₀ hu₀ u p hm T hT)

end PeriodicNSContinuation
