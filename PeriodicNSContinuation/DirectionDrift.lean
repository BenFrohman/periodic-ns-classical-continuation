/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.FrohmanianDirectionCoercivity

/-!
# Two-point direction drift, and the gap from `FrohmanianDirectionCoercivity` to (B)

* `twoPoint_direction_drift` — **proved** (abstract ODE fact): along two Lagrangian paths, if each
  direction `τ_i(t)` has rate `‖τ_i'‖ ≤ B`, then `‖δτ(t)‖ ≤ ‖δτ(0)‖ + 2B t`.

**Exact gap (on paper, not a theorem).** The vorticity equation gives `Dτ/Dt = bend + ν(I-τ⊗τ)Δω/|ω|`.
`FrohmanianDirectionCoercivity` only gives `|bend| ≤ ε|ω|`, so the drift bound needs three things:
(i) `∫₀^{T*} ‖ω‖∞ dt < ∞`, which is BKM and therefore circular;
(ii) control of the viscous term `(I-τ⊗τ)Δω/|ω|`, which nothing here bounds;
(iii) a comparison `|X(x,t)-X(y,t)| ≳ |x-y|`, which needs `∫‖∇u‖∞` and is BKM again.
The only extra hypothesis that closes the gap is BKM integrability itself, which already implies
regularity. Following the no-drift rule, no new Prop is named for it.

**Kinematic obstruction.** Pointwise high-set bounds cannot give a uniform Hölder constant. The planar family
`ω = A e_z sin(n x₁)` has `bend ≡ 0` (see `orthogonalStrain_planar`), but `τ = ±e_z` flips sign
across distance `π/n` inside `{|ω| ≥ A/2}`. Its `½`-Hölder constant is therefore at least `2√(n/π) → ∞`.
This is not a Navier–Stokes blow-up (2D flows are global), but it shows that the implication must use
the dynamics, not the pointwise bound alone.
-/

namespace PeriodicNSContinuation

/-- **Proved.** Two-point direction drift under a uniform rate bound. -/
theorem twoPoint_direction_drift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {τx τy τx' τy' : ℝ → E} {B t : ℝ} (ht : 0 ≤ t)
    (hx : ∀ s ∈ Set.Icc (0:ℝ) t, HasDerivWithinAt τx (τx' s) (Set.Icc 0 t) s)
    (hy : ∀ s ∈ Set.Icc (0:ℝ) t, HasDerivWithinAt τy (τy' s) (Set.Icc 0 t) s)
    (bx : ∀ s ∈ Set.Ico (0:ℝ) t, ‖τx' s‖ ≤ B) (by' : ∀ s ∈ Set.Ico (0:ℝ) t, ‖τy' s‖ ≤ B) :
    ‖τx t - τy t‖ ≤ ‖τx 0 - τy 0‖ + 2 * B * t := by
  have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun s => τx s - τy s)
    (f' := fun s => τx' s - τy' s) (C := 2 * B)
    (fun s hs => (hx s hs).sub (hy s hs))
    (fun s hs => by
      calc ‖τx' s - τy' s‖ ≤ ‖τx' s‖ + ‖τy' s‖ := norm_sub_le _ _
        _ ≤ 2 * B := by linarith [bx s hs, by' s hs])
    t ⟨ht, le_rfl⟩
  have h2 : ‖τx t - τy t‖ ≤ ‖τx 0 - τy 0‖ + ‖(τx t - τy t) - (τx 0 - τy 0)‖ := by
    have := norm_add_le (τx 0 - τy 0) ((τx t - τy t) - (τx 0 - τy 0))
    simpa using this
  simp only [sub_zero] at key
  linarith

end PeriodicNSContinuation
