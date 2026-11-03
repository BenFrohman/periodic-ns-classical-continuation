/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.CubicSource
import PeriodicNSContinuation.StrainLinfFamily
import PeriodicNSContinuation.IntegrabilityAttack

/-!
# `PeriodicStrainLinfBound` is false (names coined, Nov 3 2026)

* `not_periodicStrainLinfBound_of_static` (**proved**): if local existence holds, every smooth datum
  has a maximal solution, and the static bound `StaticStrainLinfBound` fails, then
  `PeriodicStrainLinfBound ν` fails. The argument evaluates the solution-level bound at `t = 0`,
  where `u 0 = u₀`.
* `not_periodicStrainLinfBound` (**proved, unconditional**, `ν > 0`): all three inputs are already
  theorems in this repository (`periodicLocalExistence_of_nonneg`,
  `periodicMaximalSolution_of_uniqueness` + `periodicEnergyDifferenceEstimate`,
  `StrainLinfFamily.not_staticStrainLinfBound`). No new hypothesis Props.
-/

open FeffermanClayNS NavierStokes3D

namespace PeriodicNSContinuation

open Corrected

/-- **Proved.** A static counterexample at `t = 0` refutes the solution-level bound, given local
existence and existence of maximal solutions. -/
theorem not_periodicStrainLinfBound_of_static {ν : ℝ} (hν : 0 < ν)
    (hloc : PeriodicLocalExistence ν) (hmax : PeriodicMaximalSolution ν)
    (hstat : ¬ StrainLinfFamily.StaticStrainLinfBound) : ¬ PeriodicStrainLinfBound ν := by
  intro h
  obtain ⟨C, _, hC⟩ := h hν
  apply hstat
  refine ⟨C, fun u₀ hu₀ x => ?_⟩
  obtain ⟨u, p, hm⟩ := hmax hν u₀ hu₀
  have hpos := hloc hν u₀ hu₀
  obtain ⟨T, hT0, hTt⟩ := EReal.lt_iff_exists_real_btwn.1 hpos
  have hsol := hm T (by exact_mod_cast hT0) hTt
  have h0 : u 0 = u₀ := funext hsol.2.2.2.2.2.2.2
  have := hC u₀ hu₀ u p hm 0 le_rfl (by exact_mod_cast hpos) x
  rwa [h0] at this

/-- **Proved, unconditional.** For every `ν > 0`, `PeriodicStrainLinfBound ν` is false. -/
theorem not_periodicStrainLinfBound {ν : ℝ} (hν : 0 < ν) : ¬ PeriodicStrainLinfBound ν :=
  not_periodicStrainLinfBound_of_static hν (periodicLocalExistence_of_nonneg hν.le)
    (periodicMaximalSolution_of_uniqueness
      (periodicVelocityUniqueness_of_energy ν (periodicEnergyDifferenceEstimate hν.le)))
    StrainLinfFamily.not_staticStrainLinfBound

end PeriodicNSContinuation
