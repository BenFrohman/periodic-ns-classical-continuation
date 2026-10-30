/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import FeffermanClayNS

/-!
# Assembling `PeriodicLocalExistence` from named inputs

**Conditional.** `periodicLocalExistence_of_inputs` derives `PeriodicLocalExistence ν` from two
named Props passed as explicit arguments, relative to an arbitrary predicate
`UniformBound : NavierStokes3D.VelocityField → ℝ → Prop` (intended: "the truncated Galerkin solutions from the
Fourier transcription of `u₀` (see `torus-fourier-ns-lemmas`, `GalerkinNS`) are bounded in `H^s`,
`s > 5/2`, uniformly in `N` on `[0,T]`").

* `PeriodicGalerkinUniformTime ν UniformBound` (coined): every smooth periodic datum has some
  `T > 0` with `UniformBound u₀ T` (the a priori estimate; uses the commutator estimate). NOT proved.
* `PeriodicGalerkinLimit ν UniformBound` (coined): a uniform bound on `[0,T]`, `T > 0`, yields a
  periodic smooth solution on `[0,T]` (compactness, passage to the limit, smoothness, pressure).
  NOT proved.

Proved here: the final step, a solution on some `T > 0` gives `0 < periodicTstar ν u₀`.
-/

namespace PeriodicNSContinuation

open FeffermanClayNS NavierStokes3D

/-- Coined name. Uniform existence time for the Galerkin approximants. -/
def PeriodicGalerkinUniformTime (_ν : ℝ) (UniformBound : NavierStokes3D.VelocityField → ℝ → Prop) : Prop :=
  ∀ u₀ : NavierStokes3D.VelocityField, IsPeriodicSmoothInitialData u₀ → ∃ T : ℝ, 0 < T ∧ UniformBound u₀ T

/-- Coined name. Passage to the limit from a uniform bound to a periodic smooth solution. -/
def PeriodicGalerkinLimit (ν : ℝ) (UniformBound : NavierStokes3D.VelocityField → ℝ → Prop) : Prop :=
  ∀ u₀ : NavierStokes3D.VelocityField, IsPeriodicSmoothInitialData u₀ → ∀ T : ℝ, 0 < T → UniformBound u₀ T →
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p

/-- Proved: a solution on a positive horizon gives a positive maximal time. -/
theorem periodicTstar_pos_of_solution {ν : ℝ} {u₀ : NavierStokes3D.VelocityField} {T : ℝ} (hT : 0 < T)
    (h : ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p) :
    (0 : EReal) < periodicTstar ν u₀ := by
  have hmem : (T : EReal) ∈ periodicExistenceTimes ν u₀ := ⟨T, rfl, h⟩
  exact lt_of_lt_of_le (by exact_mod_cast hT) (le_sSup hmem)

/-- **Conditional assembly** of `PeriodicLocalExistence ν` from the two named inputs. -/
theorem periodicLocalExistence_of_inputs (ν : ℝ) (UniformBound : NavierStokes3D.VelocityField → ℝ → Prop)
    (hTime : PeriodicGalerkinUniformTime ν UniformBound)
    (hLimit : PeriodicGalerkinLimit ν UniformBound) :
    PeriodicLocalExistence ν := by
  intro _ u₀ hu₀
  obtain ⟨T, hT, hB⟩ := hTime u₀ hu₀
  exact periodicTstar_pos_of_solution hT (hLimit u₀ hu₀ T hT hB)

end PeriodicNSContinuation
