/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.LocalExistenceProof
import PeriodicNSContinuation.Energy

/-!
# `H^s` continuation and the BKM split (names coined)

`PeriodicBKMCriterion ν` is split as
* `PeriodicHsBlowupAlternative ν s` — **proved** (`periodicHsBlowupAlternative`, `0 ≤ ν`, `5/2 < s`),
  from quantitative local existence (`periodicLocalSolution_quant`), time shift (`shift_sol`),
  uniqueness and gluing (`glue_sol`);
* `PeriodicBKMHsControl ν s` — **NOT proved** (classical BKM core: tame `H^s` estimate plus the
  logarithmic Sobolev inequality).

`periodicBKMCriterion_of_hsControl` assembles them. `PeriodicBKMIntegrability` stays the OPEN
hypothesis; Clay is not solved.
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D
open scoped ContDiff

namespace PeriodicNSContinuation

open Corrected

lemma barrierTime_anti {C Y₁ Y₂ : ℝ} (hC : 0 ≤ C) (hY₁ : 0 ≤ Y₁) (h : Y₁ ≤ Y₂) :
    TorusFourierNS.barrierTime C Y₂ ≤ TorusFourierNS.barrierTime C Y₁ := by
  unfold TorusFourierNS.barrierTime
  have h1 : (Y₁ + 1) ^ (3/2 : ℝ) ≤ (Y₂ + 1) ^ (3/2 : ℝ) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  have h0 : 0 ≤ C * (Y₁ + 1) ^ (3/2 : ℝ) := by positivity
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left h1 hC]

lemma barrierTime_pos {C Y : ℝ} (hC : 0 ≤ C) (hY : 0 ≤ Y) : 0 < TorusFourierNS.barrierTime C Y := by
  unfold TorusFourierNS.barrierTime
  have : 0 ≤ C * (Y + 1) ^ (3/2 : ℝ) := by positivity
  positivity

/-- **Proved.** Quantitative local existence: the existence time depends only on an upper bound
`Y` for `‖u₀‖_{H^s}²`. -/
theorem periodicLocalSolution_quant {ν s : ℝ} (hν : 0 ≤ ν) (hs : 5 / 2 < s)
    {u₀ : VelocityField} (hu₀ : IsPeriodicSmoothInitialData u₀) {Y : ℝ}
    (hY : TorusFourierNS.hsNormField s (fourierCoeffVF u₀) ^ 2 ≤ Y) :
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0)
        (TorusFourierNS.barrierTime (TorusFourierNS.transportConst s) Y) u p := by
  set C := TorusFourierNS.transportConst s
  have hC : 0 ≤ C := TorusFourierNS.transportConst_nonneg (by linarith)
  set a := fourierCoeffVF u₀
  have ha := periodicDataHs s u₀ hu₀
  set Y₀ := TorusFourierNS.hsNormField s a ^ 2
  have hY₀ : 0 ≤ Y₀ := sq_nonneg _
  have hE := TorusFourierNS.galerkinHsEnergyInequality_of_transport (ν := ν) hν
    (TorusFourierNS.galerkinTransportBound_of_gt hs)
  set T := TorusFourierNS.barrierTime C Y
  have hT : 0 < T := barrierTime_pos hC (hY₀.trans hY)
  have hTT : T ≤ TorusFourierNS.barrierTime C Y₀ := barrierTime_anti hC hY₀ hY
  have hStr := galerkinStructurePreserved_of ν periodicDataDivFree
  have bound : ∀ (N : ℕ) (T' : ℝ), T' ≤ T → ∀ α : ℝ → TorusFourierNS.GState N,
      IsGalerkinSolutionOn N ν a T' α → ∀ t ∈ Icc 0 T',
        TorusFourierNS.hsNormField s (TorusFourierNS.extendG (α t)) ≤ Real.sqrt (Y₀ + 1) := by
    intro N T' hT' α hα t ht
    have h := TorusFourierNS.galerkin_uniform_bound_of_energy hC hE ha (hT'.trans hTT) hα.1 hα.2
      (hStr u₀ hu₀ N T' α hα) t ht
    exact Real.le_sqrt_of_sq_le h
  have hB : GalerkinUniformBoundNS ν s u₀ T := by
    refine ⟨Real.sqrt (Y₀ + 1), fun N => ?_⟩
    obtain ⟨α, hα⟩ := galerkinContinuation ν s N a T (Real.sqrt (Y₀ + 1)) hT
      (fun T' hT' α hα => bound N T' hT'.2 α hα)
    exact ⟨α, hα, bound N T le_rfl α hα⟩
  exact periodicGalerkinLimit_of_nonneg hν hs u₀ hu₀ T hT hB


variable {ν : ℝ}

/-- **Proved.** Time shift of a solution. -/
theorem shift_sol {u₀ : VelocityField} {T a : ℝ} {u : TimeDependentVelocity}
    {p : TimeDependentPressure} (h : IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p)
    (ha : 0 ≤ a) (haT : a < T) :
    IsPeriodicSmoothSolutionOn ν (u a) (fun _ _ => 0) (T - a) (fun t => u (a + t))
      (fun t => p (a + t)) := by
  obtain ⟨hT, hpu, hpp, hcu, hcp, heq, hdiv, hinit⟩ := h
  have hm : ∀ t ∈ Icc (0:ℝ) (T - a), a + t ∈ Icc (0:ℝ) T :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hT' : 0 < T - a := by linarith
  have hmapS : MapsTo (fun q : ℝ × T3 => (a + q.1, q.2)) (Icc 0 (T - a) ×ˢ univ)
      (Icc 0 T ×ˢ univ) := fun q hq => ⟨hm q.1 hq.1, trivial⟩
  have hsm : ContDiff ℝ ∞ (fun q : ℝ × T3 => (a + q.1, q.2)) :=
    (contDiff_const.add contDiff_fst).prodMk contDiff_snd
  refine ⟨hT', fun t ht => hpu _ (hm t ht), fun t ht => hpp _ (hm t ht),
    hcu.comp hsm.contDiffOn hmapS, hcp.comp hsm.contDiffOn hmapS, ?_,
    fun t ht => hdiv _ (hm t ht), fun x => by simp⟩
  intro t ht x
  have hd := hasDerivWithinAt_slice hcu x (hm t ht)
  have hsh : HasDerivWithinAt (fun s : ℝ => a + s) 1 (Icc 0 (T - a)) t :=
    ((hasDerivAt_id' t).const_add a).hasDerivWithinAt
  have hc := hd.scomp t hsh (fun s hs => hm s hs)
  have := hc.derivWithin (uniqueDiffOn_Icc hT' t ht)
  simp only [one_smul] at this
  rw [show (fun s => u (a + s) x) = (fun s => u s x) ∘ (fun s => a + s) from rfl, this]
  exact heq _ (hm t ht) x

lemma glueR {E : Type*} {f g : ℝ → T3 → E} {T₁ a t : ℝ}
    (hag : ∀ t ∈ Icc (0:ℝ) (T₁ - a), g t = f (a + t)) (hat : a ≤ t) :
    (if t ≤ T₁ then f t else g (t - a)) = g (t - a) := by
  split_ifs with h
  · rw [hag (t - a) ⟨by linarith, by linarith⟩]; congr 1; ring
  · rfl

lemma glue_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : ℝ → T3 → E}
    {T₁ a δ : ℝ}
    (hf : ContDiffOn ℝ ∞ (fun q : ℝ × T3 => f q.1 q.2) (Icc (0:ℝ) T₁ ×ˢ univ))
    (hg : ContDiffOn ℝ ∞ (fun q : ℝ × T3 => g q.1 q.2) (Icc (0:ℝ) δ ×ˢ univ))
    (hag : ∀ t ∈ Icc (0:ℝ) (T₁ - a), g t = f (a + t)) (haT : a < T₁) :
    ContDiffOn ℝ ∞ (fun q : ℝ × T3 => (if q.1 ≤ T₁ then f q.1 else g (q.1 - a)) q.2)
      (Icc (0:ℝ) (a + δ) ×ˢ univ) := by
  apply contDiffOn_of_locally_contDiffOn
  rintro ⟨t, x⟩ ⟨ht, -⟩
  by_cases hlt : t < T₁
  · refine ⟨Iio T₁ ×ˢ univ, isOpen_Iio.prod isOpen_univ, ⟨hlt, trivial⟩, ?_⟩
    refine (hf.mono ?_).congr ?_
    · rintro ⟨s, y⟩ ⟨⟨hs, -⟩, hs', -⟩
      exact ⟨⟨hs.1, (show s < T₁ from hs').le⟩, trivial⟩
    · rintro ⟨s, y⟩ ⟨-, hs', -⟩
      simp only [if_pos (show s < T₁ from hs').le]
  · have hat : a < t ∨ a ≥ t := lt_or_ge a t
    rcases hat with hat | hat
    · refine ⟨Ioi a ×ˢ univ, isOpen_Ioi.prod isOpen_univ, ⟨hat, trivial⟩, ?_⟩
      have hsm : ContDiff ℝ ∞ (fun q : ℝ × T3 => (q.1 - a, q.2)) :=
        (contDiff_fst.sub contDiff_const).prodMk contDiff_snd
      refine (hg.comp hsm.contDiffOn ?_).congr ?_
      · rintro ⟨s, y⟩ ⟨⟨hs, -⟩, hs', -⟩
        exact ⟨⟨by linarith [show a < s from hs'], by linarith [hs.2]⟩, trivial⟩
      · rintro ⟨s, y⟩ ⟨-, hs', -⟩
        simp only [Function.comp]
        rw [glueR hag (le_of_lt (show a < s from hs'))]
    · exact absurd haT (not_lt.2 (by linarith [not_lt.1 hlt]))

lemma glue_deriv {f g : ℝ → T3 → T3} {T₁ a δ : ℝ}
    (hf : ContDiffOn ℝ ∞ (fun q : ℝ × T3 => f q.1 q.2) (Icc (0:ℝ) T₁ ×ˢ univ))
    (hg : ContDiffOn ℝ ∞ (fun q : ℝ × T3 => g q.1 q.2) (Icc (0:ℝ) δ ×ˢ univ))
    (hag : ∀ t ∈ Icc (0:ℝ) (T₁ - a), g t = f (a + t)) (haT : a < T₁) (hpos : 0 < a + δ)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) (a + δ)) (x : T3) :
    derivWithin (fun s => (if s ≤ T₁ then f s else g (s - a)) x) (Icc (0:ℝ) (a + δ)) t =
      if t < T₁ then derivWithin (fun s => f s x) (Icc (0:ℝ) T₁) t
      else derivWithin (fun s => g s x) (Icc (0:ℝ) δ) (t - a) := by
  by_cases hlt : t < T₁
  · rw [if_pos hlt]
    have hd := hasDerivWithinAt_slice hf x ⟨ht.1, hlt.le⟩
    have h2 : HasDerivWithinAt (fun s => (if s ≤ T₁ then f s else g (s - a)) x)
        (derivWithin (fun s => f s x) (Icc (0:ℝ) T₁) t) (Icc (0:ℝ) (a + δ) ∩ Iio T₁) t :=
      (hd.mono (fun s hs => ⟨hs.1.1, (show s < T₁ from hs.2).le⟩)).congr
        (fun s hs => by simp only [if_pos (show s < T₁ from hs.2).le])
        (by simp only [if_pos hlt.le])
    have h3 := (hasDerivWithinAt_inter (Iio_mem_nhds hlt)).1 h2
    exact h3.derivWithin (uniqueDiffOn_Icc hpos t ht)
  · rw [if_neg hlt]
    have hat : a < t := by linarith [not_lt.1 hlt]
    have ht' : t - a ∈ Icc (0:ℝ) δ := ⟨by linarith, by linarith [ht.2]⟩
    have hd := hasDerivWithinAt_slice hg x ht'
    have hsh : HasDerivWithinAt (fun s : ℝ => s - a) 1 (Icc a (a + δ)) t :=
      ((hasDerivAt_id' t).sub_const a).hasDerivWithinAt
    have hmap : MapsTo (fun s : ℝ => s - a) (Icc a (a + δ)) (Icc (0:ℝ) δ) :=
      fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hc := hd.scomp t hsh hmap
    simp only [one_smul] at hc
    have h2 : HasDerivWithinAt (fun s => (if s ≤ T₁ then f s else g (s - a)) x)
        (derivWithin (fun s => g s x) (Icc (0:ℝ) δ) (t - a)) (Icc (0:ℝ) (a + δ) ∩ Ioi a) t :=
      (hc.mono (fun s hs => ⟨(show a < s from hs.2).le, hs.1.2⟩)).congr
        (fun s hs => by simp only [Function.comp]; rw [glueR hag (show a < s from hs.2).le])
        (by simp only [Function.comp]; rw [glueR hag hat.le])
    have h3 := (hasDerivWithinAt_inter (Ioi_mem_nhds hat)).1 h2
    exact h3.derivWithin (uniqueDiffOn_Icc hpos t ht)

/-- **Proved.** Gluing a solution on `[0,T₁]` with a solution started at time `a < T₁` from
`u a`, which agrees with it on the overlap. -/
theorem glue_sol {u₀ : VelocityField} {T₁ a δ : ℝ} {u v : TimeDependentVelocity}
    {p q : TimeDependentPressure}
    (hu : IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T₁ u p)
    (hv : IsPeriodicSmoothSolutionOn ν (u a) (fun _ _ => 0) δ v q)
    (ha : 0 ≤ a) (haT : a < T₁)
    (hagU : ∀ t ∈ Icc (0:ℝ) (T₁ - a), v t = u (a + t))
    (hagP : ∀ t ∈ Icc (0:ℝ) (T₁ - a), q t = p (a + t)) :
    IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) (a + δ)
      (fun t => if t ≤ T₁ then u t else v (t - a))
      (fun t => if t ≤ T₁ then p t else q (t - a)) := by
  obtain ⟨hT₁, hpu, hpp, hcu, hcp, heq, hdiv, hinit⟩ := hu
  obtain ⟨hδ, hpv, hpq, hcv, hcq, heqv, hdivv, hinitv⟩ := hv
  have hpos : 0 < a + δ := by linarith
  have hR : ∀ t, a < t → t ≤ a + δ → t - a ∈ Icc (0:ℝ) δ :=
    fun t h1 h2 => ⟨by linarith, by linarith⟩
  refine ⟨hpos, ?_, ?_, glue_contDiffOn hcu hcv hagU haT, glue_contDiffOn hcp hcq hagP haT,
    ?_, ?_, ?_⟩
  · intro t ht
    by_cases h : t ≤ T₁
    · simp only [if_pos h]; exact hpu t ⟨ht.1, h⟩
    · simp only [if_neg h]; exact hpv _ (hR t (by linarith [not_le.1 h]) ht.2)
  · intro t ht
    by_cases h : t ≤ T₁
    · simp only [if_pos h]; exact hpp t ⟨ht.1, h⟩
    · simp only [if_neg h]; exact hpq _ (hR t (by linarith [not_le.1 h]) ht.2)
  · intro t ht x
    rw [glue_deriv hcu hcv hagU haT hpos ht x]
    by_cases hlt : t < T₁
    · simp only [if_pos hlt, if_pos hlt.le]; exact heq t ⟨ht.1, hlt.le⟩ x
    · have hat : a < t := by linarith [not_lt.1 hlt]
      simp only [if_neg hlt]
      rw [glueR hagU hat.le, glueR hagP hat.le]
      exact heqv _ (hR t hat ht.2) x
  · intro t ht x
    by_cases h : t ≤ T₁
    · simp only [if_pos h]; exact hdiv t ⟨ht.1, h⟩ x
    · simp only [if_neg h]; exact hdivv _ (hR t (by linarith [not_le.1 h]) ht.2) x
  · intro x
    simp only [if_pos hT₁.le]; exact hinit x

/-- **Coined. Proved for `0 ≤ ν`, `s > 5/2`** (`periodicHsBlowupAlternative`): a maximal solution
with finite `T*` is unbounded in `H^s` on `[0, T*)`. -/
def PeriodicHsBlowupAlternative (ν s : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsPeriodicMaximalSolution ν u₀ u p →
      ∀ T : ℝ, periodicTstar ν u₀ = (T : EReal) →
        ¬ ∃ M : ℝ, ∀ t ∈ Ico (0:ℝ) T, TorusFourierNS.hsNormField s (fourierCoeffVF (u t)) ≤ M

/-- **Proved.** The `H^s` blow-up alternative, for `ν ≥ 0` and `s > 5/2`: a maximal solution
with finite `T*` cannot stay bounded in `H^s` on `[0, T*)`. -/
theorem periodicHsBlowupAlternative {s : ℝ} (hν : 0 ≤ ν) (hs : 5 / 2 < s) :
    PeriodicHsBlowupAlternative ν s := by
  intro hν' u₀ hu₀ u p hmax T hT ⟨M, hM⟩
  have hTpos : 0 < T := by
    have := periodicLocalExistence_of_nonneg hν hν' u₀ hu₀
    rw [hT] at this; exact_mod_cast this
  set C := TorusFourierNS.transportConst s
  have hC : 0 ≤ C := TorusFourierNS.transportConst_nonneg (by linarith)
  set δ := TorusFourierNS.barrierTime C (M ^ 2)
  have hδ : 0 < δ := barrierTime_pos hC (sq_nonneg M)
  set a := max 0 (T - δ / 2)
  set T₁ := (a + T) / 2
  have ha : 0 ≤ a := le_max_left _ _
  have ha' : T - δ / 2 ≤ a := le_max_right _ _
  have haT : a < T := max_lt hTpos (by linarith)
  have haT₁ : a < T₁ := by simp only [T₁]; linarith
  have hT₁T : T₁ < T := by simp only [T₁]; linarith
  have hT₁δ : T₁ - a ≤ δ := by simp only [T₁]; linarith
  have hu₁ : IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T₁ u p :=
    hmax T₁ (by linarith) (by rw [hT]; exact_mod_cast hT₁T)
  have haI : a ∈ Icc (0:ℝ) T₁ := ⟨ha, haT₁.le⟩
  have hua : IsPeriodicSmoothInitialData (u a) :=
    ⟨contDiff_slice hu₁.2.2.2.1 haI, fun x => hu₁.2.2.2.2.2.2.1 a haI x, hu₁.2.1 a haI⟩
  have hbd : TorusFourierNS.hsNormField s (fourierCoeffVF (u a)) ^ 2 ≤ M ^ 2 :=
    pow_le_pow_left₀ (by unfold TorusFourierNS.hsNormField; exact Real.sqrt_nonneg _)
      (hM a ⟨ha, haT⟩) 2
  obtain ⟨v, q, hv⟩ := periodicLocalSolution_quant hν hs hua hbd
  have hsh := shift_sol hu₁ ha haT₁
  have hpos₁ : 0 < T₁ - a := by linarith
  have hv₁ := restrict hv hpos₁ hT₁δ
  have huniq := periodicVelocityUniqueness_of_energy ν (periodicEnergyDifferenceEstimate hν)
  have hagU : ∀ t ∈ Icc (0:ℝ) (T₁ - a), v t = u (a + t) :=
    fun t ht => huniq (u a) _ v _ q _ hv₁ hsh t ht
  have hv₁' := congr hv₁ (u' := fun t => u (a + t)) (p' := q)
    (fun t ht => (hagU t ht).symm) (fun _ _ => rfl)
  have hagP : ∀ t ∈ Icc (0:ℝ) (T₁ - a), normP q t = normP p (a + t) :=
    fun t ht => normP_eq_of_velocity_eq hv₁' hsh t ht
  have hw := glue_sol (normP_sol hu₁) (normP_sol hv) ha haT₁ hagU hagP
  have hmem : ((a + δ : ℝ) : EReal) ∈ periodicExistenceTimes ν u₀ := ⟨a + δ, rfl, _, _, hw⟩
  have hle := le_sSup hmem
  rw [← periodicTstar, hT] at hle
  have : a + δ ≤ T := by exact_mod_cast hle
  linarith

/-- **Coined, NOT proved (classical BKM core).** Along a maximal solution with finite `T*`,
integrability of `‖ω‖_∞` on `[0, T*]` bounds `‖u(t)‖_{H^s}` on `[0, T*)`. -/
def PeriodicBKMHsControl (ν s : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsPeriodicMaximalSolution ν u₀ u p →
      ∀ T : ℝ, periodicTstar ν u₀ = (T : EReal) →
        IntegrableOn (fun t => vorticity_sup_norm (vorticity (u t))) (Icc 0 T) →
        ∃ M : ℝ, ∀ t ∈ Ico (0:ℝ) T, TorusFourierNS.hsNormField s (fourierCoeffVF (u t)) ≤ M

/-- **Conditional assembly.** `PeriodicBKMCriterion` from `PeriodicBKMHsControl` (the blow-up
alternative is proved). -/
theorem periodicBKMCriterion_of_hsControl {s : ℝ} (hν : 0 ≤ ν) (hs : 5 / 2 < s)
    (h : PeriodicBKMHsControl ν s) : PeriodicBKMCriterion ν :=
  fun hν' u₀ hu₀ u p hm T hT hint =>
    periodicHsBlowupAlternative hν hs hν' u₀ hu₀ u p hm T hT (h hν' u₀ hu₀ u p hm T hT hint)

/-- **Conditional reduction.** Statement (B) from `PeriodicBKMHsControl ν s` (some `s > 5/2`)
and the OPEN `PeriodicBKMIntegrability ν`. Does not prove Statement (B). -/
theorem clay_B_exact_of_hsControl (ν s : ℝ) (hs : 5 / 2 < s) (hctrl : PeriodicBKMHsControl ν s)
    (hint : PeriodicBKMIntegrability ν) : Clay_B_exact ν := fun hν =>
  clay_B_exact_of_bkm ν (periodicBKMCriterion_of_hsControl hν.le hs hctrl) hint hν

end PeriodicNSContinuation
