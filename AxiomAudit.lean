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
#print axioms PeriodicNSContinuation.eventually_mem_modeBox
#print axioms PeriodicNSContinuation.limit_initial
#print axioms PeriodicNSContinuation.hermitian_of_tendsto
#print axioms PeriodicNSContinuation.divergenceFree_of_tendsto
#print axioms PeriodicNSContinuation.summable_hs_extendG
#print axioms PeriodicNSContinuation.hs_of_tendsto
#print axioms PeriodicNSContinuation.periodicGalerkinLimit_of
#print axioms PeriodicNSContinuation.exists_subseq_tendsto_of_equiLipschitz
#print axioms PeriodicNSContinuation.norm_extendG_le_of_hs
#print axioms PeriodicNSContinuation.galerkinModeConvergence_of
#print axioms PeriodicNSContinuation.periodicGalerkinLimit_of'
#print axioms PeriodicNSContinuation.ptBound_of_hs
#print axioms PeriodicNSContinuation.ptBound_of_tendsto
#print axioms PeriodicNSContinuation.bse_le
#print axioms PeriodicNSContinuation.abs_le_bse_half
#print axioms PeriodicNSContinuation.norm_convTerm_le
#print axioms PeriodicNSContinuation.summable_convTerm
#print axioms PeriodicNSContinuation.norm_tsum_convTerm_le
#print axioms PeriodicNSContinuation.norm_lerayP_le
#print axioms PeriodicNSContinuation.norm_fourierNSField_le
#print axioms PeriodicNSContinuation.galerkinNSField_eq
#print axioms PeriodicNSContinuation.galerkin_component
#print axioms PeriodicNSContinuation.galerkinModeEquiLipschitz
#print axioms PeriodicNSContinuation.tendsto_fourierNSField
#print axioms PeriodicNSContinuation.galerkinLimitEquation
#print axioms PeriodicNSContinuation.periodicGalerkinLimit_of_reconstruction
#print axioms PeriodicNSContinuation.phase_periodic
#print axioms PeriodicNSContinuation.seriesC_periodic
#print axioms PeriodicNSContinuation.seriesVelocity_periodic
#print axioms PeriodicNSContinuation.seriesPressure_periodic
#print axioms PeriodicNSContinuation.conj_phase
#print axioms PeriodicNSContinuation.conj_seriesC_of_hermitian
#print axioms PeriodicNSContinuation.neg_lerayP_eq
#print axioms PeriodicNSContinuation.fourierNSField_eq_pressure
#print axioms PeriodicNSContinuation.fourierSolutionReconstruction_of
#print axioms PeriodicNSContinuation.periodicGalerkinLimit_of_subProps
#print axioms PeriodicNSContinuation.mFourierCoeff_torusCompC
#print axioms PeriodicNSContinuation.summable_norm_fourierCoeffVF
#print axioms PeriodicNSContinuation.fourierCoeffVF_hasSum
#print axioms PeriodicNSContinuation.seriesVelocity_zero
#print axioms PeriodicNSContinuation.fourierSeriesVelocity_of
#print axioms PeriodicNSContinuation.periodicGalerkinLimit_of_subProps'
#print axioms PeriodicNSContinuation.hsNormField_extendG_mono
#print axioms PeriodicNSContinuation.hs_bound_of_galerkin
#print axioms PeriodicNSContinuation.periodicGalerkinLimit_of_velocity_pressure
#print axioms PeriodicNSContinuation.CurveHyp.contDiffOn_infty
#print axioms PeriodicNSContinuation.CurveHyp.contDiffOn_seriesVelocity
#print axioms PeriodicNSContinuation.div_seriesVelocity
#print axioms PeriodicNSContinuation.seriesC_mul
#print axioms PeriodicNSContinuation.seriesC_convective
#print axioms PeriodicNSContinuation.CurveHyp.contDiffOn_seriesPressure
#print axioms PeriodicNSContinuation.CurveHyp.momentum
#print axioms PeriodicNSContinuation.fourierSeriesVelocitySmooth_of_modeCont
#print axioms PeriodicNSContinuation.periodicPressureRecovery_of_modeCont
#print axioms PeriodicNSContinuation.modeContinuous_of_tendsto
#print axioms PeriodicNSContinuation.periodicGalerkinLimit_of_nonneg
