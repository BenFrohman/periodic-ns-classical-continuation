/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.TetherClaimAttack
import PeriodicNSContinuation.KatoPonce

/-!
# Headline check: does tether geometric control give `VortDirHolderHalf` for plain NS (κ = 0)?

The tether correction in `NS_Millennium_Proof/Modules/SymplecticTether.lean:349` is
`B(F,G)(ω) = −κ ∫ |ω|² (Π_u δF · Π_u δG)`. Its claimed geometric control is (C3), at
`SymplecticTether.lean:386`: "after `Π_u`, the correction is negative-semidefinite".

Here `tetherForm κ ω g = −κ ∫_cell |ω|² |g|²`, where `g` plays the role of `Π_u δF`. Any
pointwise choice of `Π_u` gives the same result, because the factor `κ` multiplies everything.

* `tetherForm_zero` — **proved**: at `κ = 0` the form is identically `0`.
* `tetherGeometricControl_zero` — **proved**: at `κ = 0` the control holds for *every* field.
  It carries no information about plain NS.
* `tetherImpliesDirection_zero_iff` — **proved**: the headline Prop at `κ = 0` is *equivalent* to
  the open `PeriodicDirectionRegularity ν`.

**Exact failing step.** The hypothesis is vacuous at `κ = 0`, so proving the implication means
proving Definition 7.1 for every plain-NS solution, which is open. The only depletion in the
author's chain comes from the `κ`-term (`−κ''M³`). At `κ = 0` the Lyapunov functional
`S_ε = ∫ ½|ω_ε|² + (κ/4)|ω_ε|⁴φ_ε` (`TetheredLyapunov.lean`, `LyapunovS`) reduces to half the
enstrophy. Its derivative is the enstrophy identity `−ν‖∇ω‖² + ∫ ω·Sω`. No direction or
geometric term survives, and the stretching term `∫ ω·Sω` has no sign.
-/

noncomputable section
open Set FeffermanClayNS NavierStokes3D

namespace PeriodicNSContinuation

open Corrected

/-- Coined. The tether quadratic form `−κ ∫_cell |ω|² |g|²` (with `g` standing for `Π_u δF`). -/
def tetherForm {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] (κ : ℝ)
    (ω : T3 → E) (g : T3 → F) : ℝ :=
  -κ * cellI (fun x => ‖ω x‖ ^ 2 * ‖g x‖ ^ 2)

/-- **Proved.** At `κ = 0` the tether form vanishes identically. -/
theorem tetherForm_zero {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (ω : T3 → E) (g : T3 → F) : tetherForm 0 ω g = 0 := by simp [tetherForm]

/-- Coined. The tether geometric control (C3) along `u` on `[0,T)`: the form is `≤ 0` for every
test field `g`. -/
def TetherGeometricControl (κ : ℝ) (u : TimeDependentVelocity) (T : ℝ) : Prop :=
  ∀ t ∈ Ico (0:ℝ) T, ∀ g : T3 → EuclideanSpace ℝ (Fin 3), tetherForm κ (vorticity (u t)) g ≤ 0

/-- **Proved.** At `κ = 0` the control holds for every velocity field. -/
theorem tetherGeometricControl_zero (u : TimeDependentVelocity) (T : ℝ) :
    TetherGeometricControl 0 u T := fun _ _ g => by rw [tetherForm_zero]

/-- Coined. **Headline Prop.** For plain NS, tether geometric control at strength `κ` implies
Definition 7.1 (`VortDirHolderHalf`) up to any finite lifespan. -/
def PeriodicTetherImpliesDirection (κ ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure), IsPeriodicMaximalSolution ν u₀ u p →
      ∀ T : ℝ, periodicTstar ν u₀ = (T : EReal) →
        TetherGeometricControl κ u T → VortDirHolderHalf u T

/-- **Proved.** At `κ = 0` the headline Prop is exactly the open direction regularity. -/
theorem tetherImpliesDirection_zero_iff (ν : ℝ) :
    PeriodicTetherImpliesDirection 0 ν ↔ PeriodicDirectionRegularity ν := by
  constructor
  · intro h hν u₀ hu₀ u p hm T hT
    exact h hν u₀ hu₀ u p hm T hT (tetherGeometricControl_zero u T)
  · intro h hν u₀ hu₀ u p hm T hT _
    exact h hν u₀ hu₀ u p hm T hT

/-- **Proved (conditional).** The headline Prop at `κ = 0` plus the classical direction criterion
give `PeriodicBKMIntegrability`. Both hypotheses are unproved, and the first is open. -/
theorem periodicBKMIntegrability_of_tetherKappaZero {ν : ℝ} (hD : PeriodicDirectionCriterion ν)
    (h : PeriodicTetherImpliesDirection 0 ν) : PeriodicBKMIntegrability ν :=
  periodicBKMIntegrability_of_direction hD ((tetherImpliesDirection_zero_iff ν).1 h)

end PeriodicNSContinuation
