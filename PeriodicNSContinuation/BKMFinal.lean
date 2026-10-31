/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.LowFreqAssembly
import PeriodicNSContinuation.CommutatorAssembly
import PeriodicNSContinuation.LocalExistenceProof

/-!
# Unconditional `H³` BKM control and the BKM criterion

With `periodicLowFreqVorticityBound` proved, the `H³` control and the periodic BKM criterion
hold with no hypothesis Props. Statement (B) is reduced to the **open**
`PeriodicBKMIntegrability ν` alone. This does **not** prove Statement (B) or the Clay problem.
-/

open Set MeasureTheory FeffermanClayNS NavierStokes3D TorusFourierNS

namespace PeriodicNSContinuation

/-- **Proved, no hypotheses.** BKM-type `H³` control on `T³`. -/
theorem periodicBKMHsControl_three (ν : ℝ) : PeriodicBKMHsControl ν 3 :=
  periodicBKMHsControl_three_of_lowFreq ν periodicLowFreqVorticityBound

/-- **Proved, no hypotheses.** The periodic Beale–Kato–Majda criterion. -/
theorem periodicBKMCriterion (ν : ℝ) : PeriodicBKMCriterion ν := fun hν =>
  periodicBKMCriterion_of_hsControl hν.le (by norm_num) (periodicBKMHsControl_three ν) hν

/-- **Conditional only on the OPEN `PeriodicBKMIntegrability ν`.** Statement (B) of
`FeffermanClayNS`. This does not prove Statement (B). -/
theorem clay_B_exact_of_integrability (ν : ℝ) (hint : PeriodicBKMIntegrability ν) :
    Clay_B_exact ν :=
  clay_B_exact_of_bkm ν (periodicBKMCriterion ν) hint

end PeriodicNSContinuation
