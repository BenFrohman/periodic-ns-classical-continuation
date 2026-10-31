/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
-- Kernel axiom audit. Run: `lake env lean AxiomAudit.lean`.
-- Fails if any declaration in the `PeriodicNSContinuation` module tree depends on an axiom outside
-- {propext, Classical.choice, Quot.sound} (for example `sorryAx`).
import Lean
import PeriodicNSContinuation

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut thms := 0
  let mut defs := 0
  let mut bad : Array String := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`PeriodicNSContinuation).isPrefixOf mod do continue
    if n.isInternal then continue
    match ci with
    | .thmInfo _ => thms := thms + 1
    | .defnInfo _ => defs := defs + 1
    | _ => pure ()
    let axs ← liftCoreM (Lean.collectAxioms n)
    for a in axs do
      unless allowed.contains a do bad := bad.push s!"{n} uses {a}"
  logInfo m!"AxiomAudit: {thms} theorems, {defs} definitions in PeriodicNSContinuation"
  if bad.isEmpty then
    logInfo "AxiomAudit PASS: only propext, Classical.choice, Quot.sound"
  else
    throwError m!"AxiomAudit FAIL:\n{String.intercalate "\n" bad.toList}"
#print axioms PeriodicNSContinuation.sobolev_embedding_continuous
#print axioms PeriodicNSContinuation.summable_sobolevWeight_neg
#print axioms PeriodicNSContinuation.sobolevNormSq_zero
#print axioms PeriodicNSContinuation.fourierCoeffVF_hermitian
#print axioms PeriodicNSContinuation.galerkinStructurePreserved_of
#print axioms PeriodicNSContinuation.periodicGalerkinUniformTime_of_gt
#print axioms PeriodicNSContinuation.integral_pdC_eq_zero
#print axioms PeriodicNSContinuation.cubeCoeff_pdC
#print axioms PeriodicNSContinuation.periodicDataDivFree
#print axioms PeriodicNSContinuation.cubeCoeff_helmOp
#print axioms PeriodicNSContinuation.exists_bound_cubeCoeff
#print axioms PeriodicNSContinuation.summable_sobW_cubeCoeff
#print axioms PeriodicNSContinuation.periodicDataHs
#print axioms PeriodicNSContinuation.galerkinContinuation
#print axioms PeriodicNSContinuation.periodicGalerkinUniformTime_of_gt'
