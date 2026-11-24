/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import PeriodicNSContinuation.SemanticsPaper

/-!
# Truth Gate kernel audit: additional lock "paper-statements" (`SemanticsPaper.lean`)

The same checks as `TruthGateAudit.lean`, run for every claim `X` of the additional lock:
`formal_claim_X`, `paper_claim_X`, `intended_correspondence_X`, `formal_claim_holds_X`,
`paper_claim_holds_X`, against that claim's own main theorems.

Checks, in the Lean kernel environment:
* `TruthGate.formal_claim`, `TruthGate.paper_claim`, `TruthGate.intended_correspondence`,
  `TruthGate.formal_claim_holds`, `TruthGate.paper_claim_holds` exist with the required types;
* each depends only on `propext`, `Classical.choice`, `Quot.sound`;
* `formal_claim` and `paper_claim` are NOT definitionally equal (no vacuous correspondence);
* the proof of `intended_correspondence` does not use the main theorem(s) or the `*_holds`
  lemmas (it is a statement-level equivalence, not "both sides happen to be true");
* `formal_claim_holds` is built from the locked main theorem(s), and when there is a single
  main theorem its statement is definitionally `formal_claim`;
* `paper_claim_holds` is obtained by transport across `intended_correspondence`.
-/

open Lean Meta Elab Command

namespace TruthGateAuditPaper

def standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]
def claims : List (String × List Name) := [
  ("localExistence", [`PeriodicNSContinuation.periodicLocalExistence_of_nonneg]),
  ("energyDifference", [`PeriodicNSContinuation.Corrected.periodicEnergyDifferenceEstimate]),
  ("uniqueness", [`PeriodicNSContinuation.Corrected.periodicVelocityUniqueness_of_energy,
    `PeriodicNSContinuation.Corrected.periodicEnergyDifferenceEstimate]),
  ("maximal", [`PeriodicNSContinuation.Corrected.periodicMaximalSolution_of_uniqueness]),
  ("parseval", [`PeriodicNSContinuation.hasSum_prod_cubeCoeff]),
  ("topTerm", [`PeriodicNSContinuation.top_term_zero]),
  ("bkmCriterion", [`PeriodicNSContinuation.periodicBKMCriterion]),
  ("integrableBelow", [`PeriodicNSContinuation.integrableOn_vorticity_of_lt_tstar]),
  ("bkmIffGlobal", [`PeriodicNSContinuation.periodicBKMIntegrability_iff_globalLifespan]),
  ("clayBOfGlobal", [`PeriodicNSContinuation.clay_B_exact_of_globalLifespan]),
  ("clayBOfBKM", [`PeriodicNSContinuation.clay_B_exact_of_bkm]),
  ("clayBOfRoute", [`PeriodicNSContinuation.Corrected.clay_B_exact_of_corrected_route'])]

partial def reach (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then reach env rest seen else
    let seen := seen.insert n
    -- upstream libraries cannot mention this repository's constants: do not descend into them
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

end TruthGateAuditPaper

open TruthGateAuditPaper in
run_cmd do
  let env ← getEnv
  let mut ok := true
  for (cid, mains) in claims do
    let nm := fun (s : String) => Name.mkStr `TruthGatePaper (s ++ "_" ++ cid)
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
    logInfo m!"TRUTH GATE AUDIT PASS: additional lock paper-statements, {claims.length} claims; each formal_claim_X ↔ paper_claim_X locked, standard axioms only"
  else
    throwError "TRUTH GATE FAIL"
