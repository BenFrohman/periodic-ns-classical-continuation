/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.SmoothReconstruction
import PeriodicNSContinuation.FourierData
import PeriodicNSContinuation.Route

/-!
# Local existence with no hypothesis Props (names coined)

**Proved:** `periodicLocalExistence_of_nonneg (0 ≤ ν) : PeriodicLocalExistence ν`, which
discharges the `PeriodicLocalExistence` hypothesis in `FeffermanClayNS`.
`PeriodicLocalExistence` does not quantify over `s`; the proof uses `s = 3`.

**Proved (conditional reduction):** `clay_B_exact_of_bkm`:
`PeriodicBKMCriterion ν → PeriodicBKMIntegrability ν → Clay_B_exact ν`.
`PeriodicBKMIntegrability` is open, so this does **not** prove Statement (B).
-/

open FeffermanClayNS NavierStokes3D

namespace PeriodicNSContinuation

/-- **Proved (`ν ≥ 0`), no hypothesis Props.** Classical local existence (`s = 3`). -/
theorem periodicLocalExistence_of_nonneg {ν : ℝ} (hν : 0 ≤ ν) : PeriodicLocalExistence ν :=
  periodicLocalExistence_of_galerkin ν 3
    (periodicGalerkinUniformTime_of_gt' hν (by norm_num))
    (periodicGalerkinLimit_of_nonneg hν (by norm_num))

/-- **Conditional reduction.** Statement (B) from the BKM criterion and the open BKM
integrability hypothesis. This does not prove Statement (B). -/
theorem clay_B_exact_of_bkm (ν : ℝ) (hcrit : PeriodicBKMCriterion ν)
    (hint : PeriodicBKMIntegrability ν) : Clay_B_exact ν := fun hν =>
  Corrected.clay_B_exact_of_corrected_route' ν (periodicLocalExistence_of_nonneg hν.le)
    hcrit hint hν

end PeriodicNSContinuation
