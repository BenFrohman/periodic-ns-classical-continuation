# Axiom audit (commit `33e0cbf`)

Run: `lake env lean AxiomAudit.lean`.

**Summary.** `PeriodicNSContinuation` contains **1048** theorems and **285** definitions.
Every declaration in that module tree depends only on Lean's standard axioms
`propext`, `Classical.choice`, and `Quot.sound`. There is no `sorry` / `sorryAx` and no
custom axiom. This repository does **not** prove Clay Statement (B) or Navier–Stokes
regularity; the headline result `clay_B_exact_of_integrability` is a conditional reduction
whose only hypothesis is the open Prop `PeriodicBKMIntegrability`.

## Modelling note (Clay statements)

`T3` is `EuclideanSpace ℝ (Fin 3)` (ℝ³ standing in for 𝕋³), with `IsZ3Periodic` and
unit-cell integrals (`torusIntegral`). See the README Modelling section. All Clay / BKM
claims below are in that model.

## `#print axioms` — unconditional headlines

| Declaration | Axioms |
|---|---|
| `PeriodicNSContinuation.periodicBKMHsControl_three` | `propext`, `Classical.choice`, `Quot.sound` |
| `PeriodicNSContinuation.periodicBKMCriterion` | `propext`, `Classical.choice`, `Quot.sound` |
| `PeriodicNSContinuation.periodicHsBlowupAlternative` | `propext`, `Classical.choice`, `Quot.sound` |
| `PeriodicNSContinuation.periodicLocalExistence_of_nonneg` | `propext`, `Classical.choice`, `Quot.sound` |
| `PeriodicNSContinuation.Corrected.periodicEnergyDifferenceEstimate` | `propext`, `Classical.choice`, `Quot.sound` |
| `PeriodicNSContinuation.Corrected.periodicMaximalSolution_of_uniqueness` | `propext`, `Classical.choice`, `Quot.sound` |
| `PeriodicNSContinuation.Corrected.periodicVelocityUniqueness_of_energy` | `propext`, `Classical.choice`, `Quot.sound` |
| `PeriodicNSContinuation.periodicLowFreqVorticityBound` | `propext`, `Classical.choice`, `Quot.sound` |
| `PeriodicNSContinuation.periodicPhysicalCommutatorBound` | `propext`, `Classical.choice`, `Quot.sound` |
| `FeffermanClayNS.periodicGlobalOfTstarTop` | `propext`, `Classical.choice`, `Quot.sound` |

## `#print axioms` — conditional reductions (still only standard axioms)

These theorems take ordinary `Prop` hypotheses (for example `PeriodicBKMIntegrability`).
The kernel still reports only the three standard axioms; the open content sits in the
hypothesis, not in a custom axiom.

| Declaration | Axioms | Open / named hypothesis |
|---|---|---|
| `PeriodicNSContinuation.clay_B_exact_of_integrability` | `propext`, `Classical.choice`, `Quot.sound` | `PeriodicBKMIntegrability` (**only** input; Clay core) |
| `PeriodicNSContinuation.clay_B_exact_of_bkm` | `propext`, `Classical.choice`, `Quot.sound` | `PeriodicBKMCriterion` (now proved) + `PeriodicBKMIntegrability` |
| `PeriodicNSContinuation.Corrected.clay_B_exact_of_corrected_route` | `propext`, `Classical.choice`, `Quot.sound` | local existence + energy + BKM + integrability (first three dischargeable) |
| `PeriodicNSContinuation.Corrected.clay_B_exact_of_corrected_route'` | `propext`, `Classical.choice`, `Quot.sound` | local existence + BKM + integrability (first two dischargeable) |
| `PeriodicNSContinuation.periodicBKMIntegrability_iff_globalLifespan` | `propext`, `Classical.choice`, `Quot.sound` | equivalence (both sides open / Clay-strength) |
| `PeriodicNSContinuation.periodicBKMIntegrability_of_globalLifespan` | `propext`, `Classical.choice`, `Quot.sound` | `PeriodicGlobalLifespan` |
| `PeriodicNSContinuation.globalLifespan_of_periodicBKMIntegrability` | `propext`, `Classical.choice`, `Quot.sound` | `PeriodicBKMIntegrability` |
| `PeriodicNSContinuation.clay_B_exact_of_globalLifespan` | `propext`, `Classical.choice`, `Quot.sound` | `PeriodicGlobalLifespan` |

## Side-route open Props (not used by `clay_B_exact_of_integrability`)

Named Props such as `PeriodicTetherCubicRate`, `PeriodicVorticityAPrioriBound`,
`PeriodicDirectionCriterion`, `PeriodicDirectionRegularity`,
`PeriodicBendingRateHiddenProperty`, `PeriodicDirectionEnstrophyGrowthL1`,
`PeriodicH1BlowupCriterion`, `PeriodicHolderStretchingEstimate`,
`PeriodicH2SmoothingRateStd`, `PeriodicH2RootTimeIntegrable`, and
`PeriodicH3SmoothingRate` remain open classical or coined hypotheses on alternative
routes. They are **not** arguments of `clay_B_exact_of_integrability`.

## How to reproduce

```bash
lake build
lake env lean AxiomAudit.lean
# optional per-declaration check, e.g.:
# lake env lean --run <file that `#print axioms` the names above>
```
