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

## Torus Sobolev foundation (`PeriodicNSContinuation/TorusSobolev.lean`)

`Hˢ(𝕋³)` for scalar `ℂ`-valued `L²` functions on `UnitAddTorus (Fin 3)`, defined by Fourier
weights `(1 + |k|²)ˢ`. Everything below is **proved**, with no hypotheses:

* `sobolevWeight_pos`, `sobolevWeight_mono` (monotone in `s`), `sobolevWeight_neg`.
* Norm facts: `sobolevNormSqSeq_nonneg`, `sobolevNormSqSeq_eq_zero_iff`, `sobolevNormSqSeq_smul`,
  closure under `+` and scalars (`MemSobolevSeq.add`, `MemSobolevSeq.smul`).
* `Hᵗ ⊆ Hˢ` for `s ≤ t` (`MemSobolevSeq.mono`, `sobolevNormSqSeq_mono`).
* `H⁰ = L²` by Mathlib's Parseval: `memSobolev_zero`, `sobolevNormSq_zero`
  (`‖f‖²_{H⁰} = ∫ ‖f‖²`), and `integral_sq_le_sobolevNormSq` for `s ≥ 0`.
* `summable_sobolevWeight_neg`: `∑_{k∈ℤ³} (1+|k|²)^{-s} < ∞` for `s > 3/2`.
* **Sobolev embedding** `sobolev_embedding_continuous`: for `s > 3/2`, every `f ∈ L² ∩ Hˢ` equals
  a.e. a continuous function, and its Fourier series converges to it uniformly.

Not yet done: vector-valued fields, the triangle inequality for the `Hˢ` norm, algebra/product
estimates and commutator estimates. These are still needed before `PeriodicLocalExistence`
can be discharged, so that hypothesis remains open.

## LocalExistence (added)

`periodicLocalExistence_of_inputs` is **conditional**: it derives `PeriodicLocalExistence ν` from
two named Props passed as explicit arguments, relative to a user-supplied predicate `UniformBound`:
`PeriodicGalerkinUniformTime` (uniform-in-N bound on some `T > 0`; NOT proved) and
`PeriodicGalerkinLimit` (passage to the limit to a periodic smooth solution; NOT proved). Both names
are coined. Proved unconditionally: `periodicTstar_pos_of_solution` (a solution on `T > 0` gives
`0 < periodicTstar`). The Galerkin system and the `H^s` product estimate are in
`torus-fourier-ns-lemmas` (not a dependency of this package). Clay is not solved.
