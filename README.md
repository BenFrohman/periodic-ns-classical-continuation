# periodic-ns-classical-continuation

Lean 4 + Mathlib formalization of the classical continuation steps used by the Statement (B)
route in `fefferman-clay-navier-stokes` (pinned at commit `29beb91`). It does **not** solve the
Clay Navier–Stokes problem; the open step `PeriodicBKMIntegrability` remains a hypothesis.

Build: `lake build`. Axiom check: `lake env lean AxiomAudit.lean` (only `propext`,
`Classical.choice`, `Quot.sound`; no `sorry`).

## Finding about the definitions at 29beb91 (`Refutation.lean`)

* `IsPeriodicSmoothSolutionOn` includes `IsPhysicalNSSolution`, which requires L² integrability on
  all of ℝ³. A nonzero periodic field is never in L²(ℝ³), so for nonzero data no solution exists.
  Proved: `not_periodicLocalExistence` (for ν > 0).
* `IsPeriodicMaximalSolution` quantifies over all `T < T*`, including `T ≤ 0`, but solutions require
  `0 < T`. Proved: `not_periodicMaximalSolution` (for ν > 0).

So the hypotheses of `clay_B_exact_of_periodic_bkm` there cannot all hold. This repo uses corrected
versions (`Corrected.lean`): the L²(ℝ³) clause is dropped and maximality is required only for
`0 < T`. Everything else keeps the original names and bodies.

## Fully proved

* Pressure is unique up to a function of time: `normP_eq_of_velocity_eq`.
* Grönwall step for uniqueness: `eq_zero_of_deriv_le_mul`, `periodicVelocityUniqueness_of_energy`.
* Maximal solution by gluing: `periodicMaximalSolution_of_uniqueness`.
* `periodicGlobalOfTstarTop` (no hypotheses).
* Reduction `clay_B_exact_of_corrected_route`.

## Still hypotheses (named Props)

* `PeriodicEnergyDifferenceEstimate` — classical energy inequality for the difference of two solutions.
* `PeriodicLocalExistence` — classical local existence (Kato).
* `PeriodicBKMCriterion` — classical Beale–Kato–Majda.
* `PeriodicBKMIntegrability` — open.
