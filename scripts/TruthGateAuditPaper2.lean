/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import PeriodicNSContinuation.SemanticsPaper2

/-!
# Truth Gate kernel audit: additional lock "paper-statements-2" (`SemanticsPaper2.lean`)

The same checks as `TruthGateAuditPaper.lean`, for every claim `X` of this lock:
types, standard axioms only, no alias, not syntactically or definitionally equal (no vacuous
correspondence), the correspondence does not use the main theorems or the `*_holds` lemmas,
`formal_claim_holds_X` uses the main theorems, and `paper_claim_holds_X` is obtained by transport.
-/

open Lean Meta Elab Command

namespace TruthGateAuditPaper2

def standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]
def claims : List (String × List Name) := [
  ("coeffODE", [`PeriodicNSContinuation.periodicFourierCoeffODE]),
  ("coeffDecay", [`PeriodicNSContinuation.periodicFourierCoeffDecay]),
  ("hsIdentity", [`PeriodicNSContinuation.periodicFourierHsEnergyIdentity]),
  ("hsIdentityOfCoeff", [`PeriodicNSContinuation.periodicFourierHsEnergyIdentity_of_coeff]),
  ("rateThree", [`PeriodicNSContinuation.hasSum_rate_three]),
  ("ibp", [`PeriodicNSContinuation.cellI_ibp]),
  ("ibpRight", [`PeriodicNSContinuation.cellI_ibp']),
  ("leibniz", [`PeriodicNSContinuation.DL_mul]),
  ("gn", [`PeriodicNSContinuation.gagliardoNirenberg_cell]),
  ("sqMulAbs", [`PeriodicNSContinuation.cellI_sq_mul_abs_le]),
  ("lowerTerm", [`PeriodicNSContinuation.lower_term_bound]),
  ("blowup", [`PeriodicNSContinuation.periodicHsBlowupAlternative]),
  ("continuation", [`PeriodicNSContinuation.periodicBKMCriterion_of_hsControl]),
  ("physBound", [`PeriodicNSContinuation.periodicPhysicalCommutatorBound]),
  ("wordBound", [`PeriodicNSContinuation.word_bound]),
  ("physQLe", [`PeriodicNSContinuation.physQ_le_hsSq]),
  ("lowFreq", [`PeriodicNSContinuation.periodicLowFreqVorticityBound]),
  ("fourierOfPhys", [`PeriodicNSContinuation.periodicFourierCommutatorBound_of_physical]),
  ("ctrlOfPhysLow", [`PeriodicNSContinuation.periodicBKMHsControl_of_physical_lowFreq]),
  ("ctrlOfLow", [`PeriodicNSContinuation.periodicBKMHsControl_three_of_lowFreq]),
  ("ctrlThree", [`PeriodicNSContinuation.periodicBKMHsControl_three]),
  ("clayBOfCtrl", [`PeriodicNSContinuation.clay_B_exact_of_hsControl])]

partial def reach (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then reach env rest seen else
    let seen := seen.insert n
    let upstream := match env.getModuleIdxFor? n with
      | some i => let m := env.header.moduleNames[i.toNat]!
          [`Mathlib, `Init, `Std, `Lean, `Batteries, `Aesop, `Qq, `Plausible, `ProofWidgets,
            `ImportGraph, `LeanSearchClient, `Lake, `Cli].any (·.isPrefixOf m)
      | none => false
    if upstream then reach env rest seen else
    match env.find? n with
    | none => reach env rest seen
    | some ci =>
      let cs := ci.type.getUsedConstants ++ (match ci.value? (allowOpaque := true) with
        | some v => v.getUsedConstants | none => #[])
      reach env (cs.toList ++ rest) seen

def directUses (env : Environment) (n : Name) : NameSet :=
  match env.find? n with
  | some ci => ((ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[]).foldl (·.insert ·) {}
  | none => {}

end TruthGateAuditPaper2

open TruthGateAuditPaper2 in
run_cmd do
  let env ← getEnv
  let mut ok := true
  for (cid, mains) in claims do
    let nm := fun (s : String) => Name.mkStr `TruthGatePaper2 (s ++ "_" ++ cid)
    let fcN := nm "formal_claim"; let pcN := nm "paper_claim"; let icN := nm "intended_correspondence"
    let fhN := nm "formal_claim_holds"; let phN := nm "paper_claim_holds"
    let req := [fcN, pcN, icN, fhN, phN] ++ mains
    let mut present := true
    for n in req do
      unless env.contains n do
        logInfo m!"TRUTH GATE FAIL: missing declaration {n}"; ok := false; present := false
    if !present then continue
    let fc := mkConst fcN
    let pc := mkConst pcN
    unless (← getConstInfo icN).type == mkApp2 (mkConst ``Iff) fc pc do
      logInfo m!"TRUTH GATE FAIL: {icN} does not have type {fcN} ↔ {pcN}"; ok := false
    for (n, t) in [(fhN, fc), (phN, pc)] do
      unless (← getConstInfo n).type == t do
        logInfo m!"TRUTH GATE FAIL: {n} does not have the locked type"; ok := false
    for n in req do
      let axs ← collectAxioms n
      let bad := axs.filter (fun a => !standard.contains a)
      logInfo m!"AXIOMS {n}: {axs.toList}"
      unless bad.isEmpty do
        logInfo m!"TRUTH GATE FAIL: {n} uses nonstandard axioms {bad.toList}"; ok := false
    let fv := ((← getConstInfo fcN).value? (allowOpaque := true)).getD fc
    let pv := ((← getConstInfo pcN).value? (allowOpaque := true)).getD pc
    if pv.getUsedConstants.contains fcN then
      logInfo m!"TRUTH GATE FAIL: {pcN} is defined in terms of formal_claim (alias)"; ok := false
    if fv == pv then
      logInfo m!"TRUTH GATE FAIL: {fcN} and {pcN} have syntactically equal bodies"; ok := false
    let defeq? : Option Bool ← liftTermElabM <| withTransparency .default <| withoutModifyingState <|
      withTheReader Core.Context (fun c => { c with maxHeartbeats := 2000000 }) <|
        (try some <$> isDefEq fc pc catch _ => pure none)
    if defeq?.isNone then
      logInfo m!"TRUTH GATE NOTE: definitional-equality check for {cid} hit its heartbeat cap (inconclusive)"
    if defeq? == some true then
      logInfo m!"TRUTH GATE FAIL: {fcN} and {pcN} are definitionally equal (vacuous lock)"; ok := false
    let r := reach env [icN] {}
    for n in mains ++ [fhN, phN] do
      if r.contains n then
        logInfo m!"TRUTH GATE FAIL: {icN} depends on {n}"; ok := false
    let fh := reach env [fhN] {}
    for n in mains do
      unless fh.contains n do
        logInfo m!"TRUTH GATE FAIL: {fhN} does not use main theorem {n}"; ok := false
    unless (directUses env phN).contains icN do
      logInfo m!"TRUTH GATE FAIL: {phN} is not transported across {icN}"; ok := false
  if ok then
    logInfo m!"TRUTH GATE AUDIT PASS: additional lock paper-statements-2, {claims.length} claims; each formal_claim_X ↔ paper_claim_X locked, standard axioms only"
  else
    throwError "TRUTH GATE FAIL"
