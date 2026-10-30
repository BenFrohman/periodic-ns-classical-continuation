/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.Maximal
import PeriodicNSContinuation.Energy

/-!
# Corrected route to Statement (B)

`clay_B_exact_of_corrected_route` is a **conditional reduction**. Its hypotheses:

* `PeriodicLocalExistence ν` — classical (Kato), not formalized here;
* `PeriodicBKMCriterion ν` — classical (Beale–Kato–Majda), not formalized here;
* `PeriodicBKMIntegrability ν` — **OPEN** (this is the Millennium content).

`PeriodicEnergyDifferenceEstimate`, `PeriodicMaximalSolution` and `PeriodicGlobalOfTstarTop` are no longer hypotheses: they are proved
(`Energy.lean` for `ν ≥ 0` and `Maximal.lean` here, and `periodicGlobalOfTstarTop` in `FeffermanClayNS`). This file does not prove Statement (B).
-/

open FeffermanClayNS NavierStokes3D

namespace PeriodicNSContinuation.Corrected

theorem clay_B_exact_of_corrected_route (ν : ℝ)
    (hloc : PeriodicLocalExistence ν) (henergy : PeriodicEnergyDifferenceEstimate ν)
    (hcrit : PeriodicBKMCriterion ν) (hint : PeriodicBKMIntegrability ν) :
    Clay_B_exact ν :=
  clay_B_exact_of_periodic_bkm ν hloc
    (periodicMaximalSolution_of_uniqueness (periodicVelocityUniqueness_of_energy ν henergy))
    hcrit hint

/-- The route with the energy inequality discharged (`periodicEnergyDifferenceEstimate`). Still
conditional on local existence, the BKM criterion and the open `PeriodicBKMIntegrability`. -/
theorem clay_B_exact_of_corrected_route' (ν : ℝ)
    (hloc : PeriodicLocalExistence ν) (hcrit : PeriodicBKMCriterion ν)
    (hint : PeriodicBKMIntegrability ν) : Clay_B_exact ν := fun hν =>
  clay_B_exact_of_corrected_route ν hloc (periodicEnergyDifferenceEstimate hν.le) hcrit hint hν

end PeriodicNSContinuation.Corrected
