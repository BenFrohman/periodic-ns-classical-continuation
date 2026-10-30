/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.Uniqueness

/-!
# (3) Maximal solution and the global step

* `periodicMaximalSolution_of_uniqueness`: **proved** — gluing the solutions on all horizons
  (with pressure normalised by `p t 0`) gives one maximal solution, assuming only
  `PeriodicVelocityUniqueness`.
* `periodicGlobalOfTstarTop`: **proved outright** — a maximal solution with `periodicTstar = ⊤`
  is a solution of Statement (B) on `[0, ∞)`.
-/

open FeffermanClayNS NavierStokes3D Set Filter Topology
open scoped ContDiff

namespace PeriodicNSContinuation.Corrected

variable {ν : ℝ} {u₀ : VelocityField}

/-- Some solution reaches horizon `t`. -/
def Reaches (ν : ℝ) (u₀ : VelocityField) (t : ℝ) : Prop :=
  ∃ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure),
    t ≤ T ∧ IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p

open Classical in
/-- Glued velocity. -/
noncomputable def glueU (ν : ℝ) (u₀ : VelocityField) : TimeDependentVelocity := fun t =>
  if h : Reaches ν u₀ t then h.choose_spec.choose t else 0

open Classical in
/-- Glued (normalised) pressure. -/
noncomputable def glueP (ν : ℝ) (u₀ : VelocityField) : TimeDependentPressure := fun t =>
  if h : Reaches ν u₀ t then normP h.choose_spec.choose_spec.choose t else 0

theorem glue_agree (huniq : PeriodicVelocityUniqueness ν) {T : ℝ} {w : TimeDependentVelocity}
    {q : TimeDependentPressure} (hs : IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T w q) :
    ∀ t ∈ Icc (0 : ℝ) T, glueU ν u₀ t = w t ∧ glueP ν u₀ t = normP q t := by
  intro t ht
  have hR : Reaches ν u₀ t := ⟨T, w, q, ht.2, hs⟩
  have hspec := hR.choose_spec.choose_spec.choose_spec
  set T₁ := hR.choose
  set w₁ := hR.choose_spec.choose
  set q₁ := hR.choose_spec.choose_spec.choose
  have hm : 0 < min T T₁ := lt_min hs.1 hspec.2.1
  have hs' := restrict hs hm (min_le_left _ _)
  have hs₁ := restrict hspec.2 hm (min_le_right _ _)
  have htm : t ∈ Icc (0 : ℝ) (min T T₁) := ⟨ht.1, le_min ht.2 hspec.1⟩
  have hvel : ∀ s ∈ Icc (0 : ℝ) (min T T₁), w₁ s = w s := fun s hsm =>
    huniq u₀ _ w₁ w q₁ q hs₁ hs' s hsm
  have hs₁' := congr hs₁ (u' := w) (p' := q₁) (fun s hsm => (hvel s hsm).symm) (fun _ _ => rfl)
  constructor
  · simp only [glueU, dif_pos hR]; exact hvel t htm
  · simp only [glueP, dif_pos hR]
    exact normP_eq_of_velocity_eq hs₁' hs' t htm

/-- **Proved:** `PeriodicVelocityUniqueness` gives a maximal solution (for every `u₀`). -/
theorem isPeriodicMaximalSolution_glue (huniq : PeriodicVelocityUniqueness ν) :
    IsPeriodicMaximalSolution ν u₀ (glueU ν u₀) (glueP ν u₀) := by
  intro T hT hlt
  obtain ⟨s, ⟨T', rfl, w, q, hs⟩, hTs⟩ := lt_sSup_iff.1 hlt
  have hTT : T ≤ T' := (EReal.coe_lt_coe_iff.1 hTs).le
  have hr := normP_sol (restrict hs hT hTT)
  exact congr hr (fun t ht => (glue_agree huniq hs t ⟨ht.1, ht.2.trans hTT⟩).1)
    (fun t ht => (glue_agree huniq hs t ⟨ht.1, ht.2.trans hTT⟩).2)

theorem periodicMaximalSolution_of_uniqueness (huniq : PeriodicVelocityUniqueness ν) :
    PeriodicMaximalSolution ν :=
  fun _ u₀ _ => ⟨_, _, isPeriodicMaximalSolution_glue (u₀ := u₀) huniq⟩

lemma Icc_mem_nhdsWithin_Ici_prod (t : ℝ) (x : T3) :
    Icc (0 : ℝ) (t + 1) ×ˢ (univ : Set T3) ∈ 𝓝[Ici (0 : ℝ) ×ˢ univ] (t, x) := by
  refine mem_nhdsWithin.2 ⟨Iio (t + 1) ×ˢ univ, isOpen_Iio.prod isOpen_univ,
    ⟨by simp, trivial⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨⟨ha, -⟩, ha', -⟩
  exact ⟨⟨ha', (show a < t + 1 from ha).le⟩, trivial⟩

/-- **Proved outright:** a pair solving on every positive horizon solves Statement (B). -/
theorem isPeriodicSmoothSolution_of_all {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (h : ∀ T : ℝ, 0 < T → IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p) :
    IsPeriodicSmoothSolution ν u₀ (fun _ _ => 0) u p := by
  have hS : ∀ t : ℝ, 0 ≤ t → IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) (t + 1) u p :=
    fun t ht => h (t + 1) (by linarith)
  have hmem : ∀ t, 0 ≤ t → t ∈ Icc (0 : ℝ) (t + 1) := fun t ht => ⟨ht, by linarith⟩
  refine ⟨fun t ht => (hS t ht).2.1 t (hmem t ht), fun t ht => (hS t ht).2.2.1 t (hmem t ht),
    ?_, ?_, ?_, fun t ht => (hS t ht).2.2.2.2.2.2.1 t (hmem t ht), (h 1 one_pos).2.2.2.2.2.2.2⟩
  · rintro ⟨t, x⟩ ⟨ht, -⟩
    exact ((hS t ht).2.2.2.1 (t, x) ⟨hmem t ht, trivial⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsWithin_Ici_prod t x)
  · rintro ⟨t, x⟩ ⟨ht, -⟩
    exact ((hS t ht).2.2.2.2.1 (t, x) ⟨hmem t ht, trivial⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsWithin_Ici_prod t x)
  · intro t ht x
    have hd := hasDerivWithinAt_slice (hS t ht).2.2.2.1 x (hmem t ht)
    have hnhds : Icc (0 : ℝ) (t + 1) ∈ 𝓝[Ici (0 : ℝ)] t := by
      refine mem_nhdsWithin.2 ⟨Iio (t + 1), isOpen_Iio, by simp, ?_⟩
      rintro a ⟨ha, ha'⟩
      exact ⟨ha', (show a < t + 1 from ha).le⟩
    have hd' := hd.mono_of_mem_nhdsWithin hnhds
    rw [hd'.derivWithin ((uniqueDiffOn_Ici 0) t ht)]
    exact (hS t ht).2.2.2.2.2.1 t (hmem t ht) x

/-- **Proved outright:** `PeriodicGlobalOfTstarTop`. -/
theorem periodicGlobalOfTstarTop (ν : ℝ) : PeriodicGlobalOfTstarTop ν := by
  intro _ u₀ _ u p hmax htop
  exact ⟨u, p, isPeriodicSmoothSolution_of_all
    (fun T hT => hmax T hT (by rw [htop]; exact EReal.coe_lt_top T))⟩

end PeriodicNSContinuation.Corrected
