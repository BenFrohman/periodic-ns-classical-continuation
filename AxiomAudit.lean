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
#print axioms PeriodicNSContinuation.periodicLocalExistence_of_nonneg
#print axioms PeriodicNSContinuation.clay_B_exact_of_bkm
#print axioms PeriodicNSContinuation.periodicLocalSolution_quant
#print axioms PeriodicNSContinuation.shift_sol
#print axioms PeriodicNSContinuation.glue_sol
#print axioms PeriodicNSContinuation.periodicHsBlowupAlternative
#print axioms PeriodicNSContinuation.periodicBKMCriterion_of_hsControl
#print axioms PeriodicNSContinuation.clay_B_exact_of_hsControl
#print axioms PeriodicNSContinuation.gronwall_of_hasDerivAt
#print axioms PeriodicNSContinuation.periodicGradHsControl
#print axioms PeriodicNSContinuation.periodicBKMHsControl_of_tame_log
#print axioms PeriodicNSContinuation.clay_B_exact_of_tame_log
#print axioms PeriodicNSContinuation.supNorm_continuousOn
#print axioms PeriodicNSContinuation.periodicSupNormContinuity
#print axioms PeriodicNSContinuation.periodicGradHsControl_of_bound
#print axioms PeriodicNSContinuation.periodicBKMHsControl_of_bounds
#print axioms PeriodicNSContinuation.clay_B_exact_of_bounds
#print axioms PeriodicNSContinuation.fourier_split_bound
#print axioms PeriodicNSContinuation.tailWeight_tendsto_zero
#print axioms PeriodicNSContinuation.fourier_split_eps
#print axioms PeriodicNSContinuation.tailWeight_le_rpow
#print axioms PeriodicNSContinuation.fourier_split_log
#print axioms PeriodicNSContinuation.vpWeight_eq_one
#print axioms PeriodicNSContinuation.vpWeight_eq_zero
#print axioms PeriodicNSContinuation.bkm_log_arith
#print axioms PeriodicNSContinuation.sobW_add_le
#print axioms PeriodicNSContinuation.conv_term_split
#print axioms PeriodicNSContinuation.phase_shift
#print axioms PeriodicNSContinuation.summable_mode_mul_coeff
#print axioms PeriodicNSContinuation.norm_gradCoeff
#print axioms PeriodicNSContinuation.hasSum_grad
#print axioms PeriodicNSContinuation.abs_le_of_modeSq_le
#print axioms PeriodicNSContinuation.lowGrad_eq
#print axioms PeriodicNSContinuation.entry_le
#print axioms PeriodicNSContinuation.opNorm_le_entries
#print axioms PeriodicNSContinuation.grad_tail_le
#print axioms PeriodicNSContinuation.lowGrad_norm_le
#print axioms PeriodicNSContinuation.periodicLogSobolevBKMBound_of_lowFreq
#print axioms PeriodicNSContinuation.periodicBKMHsControl_of_tame_lowFreq
#print axioms PeriodicNSContinuation.fourierNSField_eq
#print axioms PeriodicNSContinuation.visc_term_nonpos
#print axioms PeriodicNSContinuation.periodicTameHsInequality_of_fourier
#print axioms PeriodicNSContinuation.periodicBKMHsControl_of_fourier_lowFreq
#print axioms PeriodicNSContinuation.hasDerivAt_normSq_complex
#print axioms PeriodicNSContinuation.fourierCoeffVF_continuousOn
#print axioms PeriodicNSContinuation.hsSq_eq_tsum
#print axioms PeriodicNSContinuation.periodicFourierHsEnergyIdentity_of_coeff
#print axioms PeriodicNSContinuation.periodicBKMHsControl_of_coeff_lowFreq
#print axioms PeriodicNSContinuation.cubeCoeff_pdR
#print axioms PeriodicNSContinuation.cubeCoeff_mul_series
#print axioms PeriodicNSContinuation.hasDerivAt_coeff_time
#print axioms PeriodicNSContinuation.cubeCoeff_dt_eq
#print axioms PeriodicNSContinuation.convective_coeff
#print axioms PeriodicNSContinuation.leray_solve
#print axioms PeriodicNSContinuation.fourierNSField_eq_dtCoeff
#print axioms PeriodicNSContinuation.periodicFourierCoeffODE
#print axioms PeriodicNSContinuation.cubeCoeff_helmR
#print axioms PeriodicNSContinuation.jreg_decay
#print axioms PeriodicNSContinuation.dtCoeff_div
#print axioms PeriodicNSContinuation.periodicFourierCoeffDecay
#print axioms PeriodicNSContinuation.periodicFourierHsEnergyIdentity
#print axioms PeriodicNSContinuation.periodicBKMHsControl_of_commutator_lowFreq
#print axioms PeriodicNSContinuation.torusLift_mk
#print axioms PeriodicNSContinuation.continuous_torusLift
#print axioms PeriodicNSContinuation.integral_torusLift
#print axioms PeriodicNSContinuation.mFourierCoeff_torusLift
#print axioms PeriodicNSContinuation.hasSum_prod_cubeCoeff
#print axioms PeriodicNSContinuation.PerR.add_int
#print axioms PeriodicNSContinuation.PerR.liftR_int
#print axioms PeriodicNSContinuation.PerR.iterate_helmR
#print axioms PeriodicNSContinuation.cubeCoeff_iterate_helmR
#print axioms PeriodicNSContinuation.hasSum_mode_fin
#print axioms PeriodicNSContinuation.perR_convR
#print axioms PeriodicNSContinuation.cubeCoeff_convR
#print axioms PeriodicNSContinuation.nlField_eq_convR
#print axioms PeriodicNSContinuation.abs_mul_le_ksq
#print axioms PeriodicNSContinuation.leray_grad_term_bound
#print axioms PeriodicNSContinuation.hasSum_re_cubeCoeff
#print axioms PeriodicNSContinuation.summable_sq_norm_cubeCoeff
#print axioms PeriodicNSContinuation.hasSum_rate_three
#print axioms PeriodicNSContinuation.periodicFourierCommutatorBound_of_physical
#print axioms PeriodicNSContinuation.periodicBKMHsControl_of_physical_lowFreq
#print axioms PeriodicNSContinuation.cellI
#print axioms PeriodicNSContinuation.PerR.cont
#print axioms PeriodicNSContinuation.PerR.mul
#print axioms PeriodicNSContinuation.PerR.add
#print axioms PeriodicNSContinuation.PerR.const_mul
#print axioms PeriodicNSContinuation.PerR.sum
#print axioms PeriodicNSContinuation.integrableOn_cell
#print axioms PeriodicNSContinuation.cellI_add
#print axioms PeriodicNSContinuation.cellI_const_mul
#print axioms PeriodicNSContinuation.cellI_neg
#print axioms PeriodicNSContinuation.cellI_sum
#print axioms PeriodicNSContinuation.cellI_mono
#print axioms PeriodicNSContinuation.cellI_nonneg
#print axioms PeriodicNSContinuation.cellI_pdR
#print axioms PeriodicNSContinuation.pdR_mul
#print axioms PeriodicNSContinuation.pdR_add
#print axioms PeriodicNSContinuation.pdR_const_mul
#print axioms PeriodicNSContinuation.pdR_sum
#print axioms PeriodicNSContinuation.pdR_comm
#print axioms PeriodicNSContinuation.cellI_ibp
#print axioms PeriodicNSContinuation.cellI_le_two
#print axioms PeriodicNSContinuation.gagliardoNirenberg_cell
#print axioms PeriodicNSContinuation.cellI_ibp'
#print axioms PeriodicNSContinuation.cellI_sq_mul_abs_le
#print axioms PeriodicNSContinuation.bddAbove_norm_fderiv
#print axioms PeriodicNSContinuation.abs_pdR_coord_le
#print axioms PeriodicNSContinuation.DL
#print axioms PeriodicNSContinuation.PerR.DL
#print axioms PeriodicNSContinuation.DL_append
#print axioms PeriodicNSContinuation.DL_pdR
#print axioms PeriodicNSContinuation.pdR_listSum
#print axioms PeriodicNSContinuation.splits
#print axioms PeriodicNSContinuation.splits_length
#print axioms PeriodicNSContinuation.mem_splits
#print axioms PeriodicNSContinuation.splits_eq
#print axioms PeriodicNSContinuation.DL_mul
#print axioms PeriodicNSContinuation.DL_sum
#print axioms PeriodicNSContinuation.toL
#print axioms PeriodicNSContinuation.exists_toL
#print axioms PeriodicNSContinuation.toL_length
#print axioms PeriodicNSContinuation.physQ
#print axioms PeriodicNSContinuation.le_physQ
#print axioms PeriodicNSContinuation.physQ_nonneg
#print axioms PeriodicNSContinuation.abs_cellI_le
#print axioms PeriodicNSContinuation.lower_term_bound
#print axioms PeriodicNSContinuation.top_term_zero
#print axioms PeriodicNSContinuation.pdR_helmR
#print axioms PeriodicNSContinuation.DL_helmR
#print axioms PeriodicNSContinuation.cellI_helmR_mul
#print axioms PeriodicNSContinuation.wordSum
#print axioms PeriodicNSContinuation.cellI_iterate_helmR
#print axioms PeriodicNSContinuation.wordSum_sum
#print axioms PeriodicNSContinuation.helm_const_le_one
#print axioms PeriodicNSContinuation.helm_const_pos
#print axioms PeriodicNSContinuation.abs_wordSum_le
#print axioms PeriodicNSContinuation.wordSum_nonneg
#print axioms PeriodicNSContinuation.le_wordSum
#print axioms PeriodicNSContinuation.cellI_listSum
#print axioms PeriodicNSContinuation.abs_listSum_le
#print axioms PeriodicNSContinuation.word_bound
#print axioms PeriodicNSContinuation.sum_cellI_helm_three
#print axioms PeriodicNSContinuation.physQ_le_hsSq
#print axioms PeriodicNSContinuation.periodicPhysicalCommutatorBound
#print axioms PeriodicNSContinuation.exists_periodicPhysicalCommutatorBound
#print axioms PeriodicNSContinuation.periodicBKMHsControl_three_of_lowFreq
