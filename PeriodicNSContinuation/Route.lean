/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.Maximal
import PeriodicNSContinuation.Energy

/-!
# Corrected route to Statement (B)

`clay_B_exact_of_corrected_route` / `clay_B_exact_of_corrected_route'` are **conditional
reductions**. Their remaining open input is:

* `PeriodicBKMIntegrability ν` — **OPEN** (this is the Millennium content).

Local existence and the BKM criterion are formalized elsewhere in this package and can be
discharged: `periodicLocalExistence_of_nonneg` (`LocalExistenceProof.lean`) and
`periodicBKMCriterion` (`BKMFinal.lean`). The theorems below still take those Props as
arguments for modularity; the headline reduction that needs only integrability is
`clay_B_exact_of_integrability` in `BKMFinal.lean`.

`PeriodicEnergyDifferenceEstimate`, `PeriodicMaximalSolution` and `PeriodicGlobalOfTstarTop`
are proved (`Energy.lean` for `ν ≥ 0`, `Maximal.lean` here, and `periodicGlobalOfTstarTop` in
`FeffermanClayNS`). This file does not prove Statement (B).
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

/-- The route with the energy inequality discharged (`periodicEnergyDifferenceEstimate`).
Still takes local existence and the BKM criterion as arguments (both proved elsewhere:
`periodicLocalExistence_of_nonneg`, `periodicBKMCriterion`); the remaining open hypothesis is
`PeriodicBKMIntegrability`. -/
theorem clay_B_exact_of_corrected_route' (ν : ℝ)
    (hloc : PeriodicLocalExistence ν) (hcrit : PeriodicBKMCriterion ν)
    (hint : PeriodicBKMIntegrability ν) : Clay_B_exact ν := fun hν =>
  clay_B_exact_of_corrected_route ν hloc (periodicEnergyDifferenceEstimate hν.le) hcrit hint hν

end PeriodicNSContinuation.Corrected
