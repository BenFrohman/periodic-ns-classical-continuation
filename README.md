# periodic-ns-classical-continuation

Lean 4 + Mathlib formalization of the classical continuation steps used by the Statement (B)
route in `fefferman-clay-navier-stokes` (pinned at commit `ebcf109`, which has the corrected
definitions). It does **not** solve the Clay Navier–Stokes problem; the open step
`PeriodicBKMIntegrability` remains a hypothesis.

Build: `lake build`. Axiom check: `lake env lean AxiomAudit.lean` (only `propext`,
`Classical.choice`, `Quot.sound`; no `sorry`).

Dependencies: Mathlib, `fefferman-clay-navier-stokes` @ `ebcf109`,
`weighted-enstrophy-identities` @ `1df4652` (for `torusIntegral` and its derivative).

## Fully proved

* `periodicEnergyDifferenceEstimate (hν : 0 ≤ ν) : PeriodicEnergyDifferenceEstimate ν`
  (`Energy.lean`). For two classical periodic solutions with the same data, with `w = u − v`,
  `E(t) = ∫_{[0,1]³} |w|²` satisfies `E' ≤ 2C E`, where `C` bounds `‖∇v‖` on `[0,T] × [0,1]³`.
  Supporting files: `TorusIntegral.lean` (positivity), `TorusField.lean` (periodic divergence
  theorem on the unit cell), `FieldIdentities.lean` (divergence-form identities for the
  convective, viscous and pressure terms), `Clamp.lean` (time extension used to differentiate E).
* Pressure is unique up to a function of time: `normP_eq_of_velocity_eq`.
* Grönwall step: `eq_zero_of_deriv_le_mul`, `periodicVelocityUniqueness_of_energy`.
* Maximal solution by gluing: `periodicMaximalSolution_of_uniqueness`.
* `periodicGlobalOfTstarTop` (no hypotheses).
* Reductions `clay_B_exact_of_corrected_route` and `clay_B_exact_of_corrected_route'`
  (the second has no energy hypothesis).

## Still hypotheses (named Props)

* `PeriodicLocalExistence` — classical local existence (Kato). Not formalized.
* `PeriodicBKMCriterion` — classical Beale–Kato–Majda. Not formalized.
* `PeriodicBKMIntegrability` — open.
