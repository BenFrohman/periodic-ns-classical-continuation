/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import FeffermanClayNS

/-!
# Two Periodic* hypotheses of `clay_B_exact_of_periodic_bkm` are false as stated

`IsPeriodicSmoothSolutionOn` (FeffermanClayNS, commit 29beb91) contains the conjunct
`IsPhysicalNSSolution u`, which asks `∫_{ℝ³} ‖u t x‖² dx` to be integrable over all of `ℝ³`.
A nonzero `ℤ³`-periodic field never satisfies this. Separately, `IsPeriodicMaximalSolution`
quantifies over every real `T < periodicTstar`, including `T ≤ 0`, where
`IsPeriodicSmoothSolutionOn` demands `0 < T`.

Proved here, for every `ν > 0`:
* `not_periodicLocalExistence`: `¬ PeriodicLocalExistence ν` (constant data `e₀`).
* `not_periodicMaximalSolution`: `¬ PeriodicMaximalSolution ν` (zero data).

So `clay_B_exact_of_periodic_bkm` has an inconsistent hypothesis set. The corrected predicates are
in `PeriodicNSContinuation.Corrected`.
-/

open FeffermanClayNS NavierStokes3D MeasureTheory

namespace PeriodicNSContinuation

/-- The constant velocity field `e₀`. -/
noncomputable def constE0 : VelocityField := fun _ => EuclideanSpace.single 0 1

theorem constE0_initialData : IsPeriodicSmoothInitialData constE0 := by
  refine ⟨contDiff_const, ?_, ?_⟩
  · intro x; simp [div, constE0]
  · intro x k; rfl

/-- A field equal to `e₀` at `t = 0` is never an `IsPhysicalNSSolution`: `‖e₀‖² = 1` is not
integrable on `ℝ³`. -/
theorem not_isPhysicalNSSolution_of_constE0 (u : TimeDependentVelocity) (h0 : u 0 = constE0) :
    ¬ IsPhysicalNSSolution u := by
  rintro ⟨-, -, hint, -, -⟩
  have := hint 0 le_rfl
  rw [h0] at this
  simp [constE0, integrable_const_iff] at this
  have h := MeasureTheory.measure_univ_of_isAddLeftInvariant (MeasureTheory.volume : Measure T3)
  exact absurd h (measure_ne_top _ _)

/-- No horizon carries an `IsPeriodicSmoothSolutionOn` solution from `e₀`. -/
theorem periodicExistenceTimes_constE0 (ν : ℝ) : periodicExistenceTimes ν constE0 = ∅ := by
  ext s
  simp only [periodicExistenceTimes, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨T, -, u, p, hsol⟩
  have h0 : u 0 = constE0 := funext hsol.2.2.2.2.2.2.2.1
  exact not_isPhysicalNSSolution_of_constE0 u h0 hsol.2.2.2.2.2.2.2.2

theorem periodicTstar_constE0 (ν : ℝ) : periodicTstar ν constE0 = ⊥ := by
  simp [periodicTstar, periodicExistenceTimes_constE0]

/-- **Proved:** `PeriodicLocalExistence ν` is false for every `ν > 0`. -/
theorem not_periodicLocalExistence (ν : ℝ) (hν : 0 < ν) : ¬ PeriodicLocalExistence ν := by
  intro h
  have := h hν constE0 constE0_initialData
  rw [periodicTstar_constE0] at this
  exact absurd this (not_lt.2 bot_le)

/-- **Proved:** `IsPeriodicMaximalSolution` can never hold once some horizon exists, because it
requires `IsPeriodicSmoothSolutionOn` at `T = -1`, which demands `0 < -1`. -/
theorem not_isPeriodicMaximalSolution_of_mem (ν : ℝ) (u₀ : VelocityField) (T : ℝ)
    (hT : (T : EReal) ∈ periodicExistenceTimes ν u₀) (u : TimeDependentVelocity)
    (p : TimeDependentPressure) : ¬ IsPeriodicMaximalSolution ν u₀ u p := by
  intro hmax
  obtain ⟨T', hT', w, q, hsol⟩ := hT
  have hTpos : (0 : ℝ) < T' := hsol.1
  have hlt : ((-1 : ℝ) : EReal) < periodicTstar ν u₀ := by
    refine lt_of_lt_of_le ?_ (le_sSup (⟨T', rfl, w, q, hsol⟩ : (T' : EReal) ∈ periodicExistenceTimes ν u₀))
    exact EReal.coe_lt_coe_iff.2 (by linarith)
  exact absurd (hmax (-1) hlt).1 (by norm_num)

/-- The zero pair is a periodic smooth solution on `[0, 1]` from zero data. -/
theorem zero_isPeriodicSmoothSolutionOn (ν : ℝ) :
    IsPeriodicSmoothSolutionOn ν 0 (fun _ _ => 0) 1 (fun _ => 0) (fun _ => 0) := by
  refine ⟨one_pos, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, contDiffOn_const, contDiffOn_const,
    ?_, ?_, fun _ => rfl, isPhysicalNSSolution_zero⟩
  · intro t _ x
    simp [convective, laplacian, pressureGradient, gradient]
  · intro t _ x
    simp [div]

theorem zero_initialData : IsPeriodicSmoothInitialData 0 := by
  refine ⟨contDiff_const, ?_, fun _ _ => rfl⟩
  intro x; simp [div]

/-- **Proved:** `PeriodicMaximalSolution ν` is false for every `ν > 0` (zero data). -/
theorem not_periodicMaximalSolution (ν : ℝ) (hν : 0 < ν) : ¬ PeriodicMaximalSolution ν := by
  intro h
  obtain ⟨u, p, hmax⟩ := h hν 0 zero_initialData
  exact not_isPeriodicMaximalSolution_of_mem ν 0 1
    ⟨1, rfl, _, _, zero_isPeriodicSmoothSolutionOn ν⟩ u p hmax

end PeriodicNSContinuation
