/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.Maximal

/-!
# Corrected route to Statement (B)

`clay_B_exact_of_corrected_route` is a **conditional reduction**. Its hypotheses:

* `PeriodicLocalExistence ν` — classical (Kato), not formalized here;
* `PeriodicEnergyDifferenceEstimate ν` — classical energy inequality, not formalized here;
* `PeriodicBKMCriterion ν` — classical (Beale–Kato–Majda), not formalized here;
* `PeriodicBKMIntegrability ν` — **OPEN** (this is the Millennium content).

`PeriodicMaximalSolution` and `PeriodicGlobalOfTstarTop` are no longer hypotheses: they are proved
(`Maximal.lean` here, and `periodicGlobalOfTstarTop` in `FeffermanClayNS`). This file does not prove Statement (B).
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

end PeriodicNSContinuation.Corrected
