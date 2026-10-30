/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import FeffermanClayNS

/-!
# Corrected periodic horizon predicates

Same definitions as `FeffermanClayNS.HighSetDepletionAndBKM` (commit 29beb91), with two
corrections and nothing else:

1. `IsPeriodicSmoothSolutionOn` drops the conjunct `IsPhysicalNSSolution u` (its `L²(ℝ³)`
   requirement excludes every nonzero periodic field; see `Refutation.lean`).
2. `IsPeriodicMaximalSolution` quantifies only over horizons `0 < T`.

The names are kept, inside the namespace `PeriodicNSContinuation.Corrected`.
-/

open FeffermanClayNS NavierStokes3D Set Filter Topology
open scoped ContDiff

namespace PeriodicNSContinuation.Corrected

/-- Fefferman's `IsPeriodicSmoothSolutionOn` without the `IsPhysicalNSSolution` conjunct. -/
def IsPeriodicSmoothSolutionOn
    (ν : ℝ) (u₀ : VelocityField) (f : ℝ → T3 → EuclideanSpace ℝ (Fin 3))
    (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure) : Prop :=
  0 < T ∧
  (∀ t ∈ Icc (0 : ℝ) T, IsZ3Periodic (u t)) ∧
  (∀ t ∈ Icc (0 : ℝ) T, IsZ3Periodic (p t)) ∧
  ContDiffOn ℝ ∞ (fun q : ℝ × T3 => u q.1 q.2) (Icc (0 : ℝ) T ×ˢ univ) ∧
  ContDiffOn ℝ ∞ (fun q : ℝ × T3 => p q.1 q.2) (Icc (0 : ℝ) T ×ˢ univ) ∧
  (∀ t ∈ Icc (0 : ℝ) T, ∀ x : T3,
    derivWithin (fun s => u s x) (Icc (0 : ℝ) T) t + convective (u t) (u t) x =
      ν • laplacian (u t) x - pressureGradient (p t) x + f t x) ∧
  (∀ t ∈ Icc (0 : ℝ) T, ∀ x : T3, div (u t) x = 0) ∧
  (∀ x : T3, u 0 x = u₀ x)

/-- Fefferman's predicate implies the corrected one. -/
theorem of_original {ν : ℝ} {u₀ : VelocityField} {f : ℝ → T3 → EuclideanSpace ℝ (Fin 3)}
    {T : ℝ} {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (h : FeffermanClayNS.IsPeriodicSmoothSolutionOn ν u₀ f T u p) :
    IsPeriodicSmoothSolutionOn ν u₀ f T u p :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1⟩

/-- Horizons on which a corrected periodic smooth solution from `u₀` exists. -/
def periodicExistenceTimes (ν : ℝ) (u₀ : VelocityField) : Set EReal :=
  {s | ∃ T : ℝ, s = (T : EReal) ∧ ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
    IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p}

/-- Maximal periodic existence time. -/
noncomputable def periodicTstar (ν : ℝ) (u₀ : VelocityField) : EReal :=
  sSup (periodicExistenceTimes ν u₀)

/-- Solves on every horizon `0 < T < periodicTstar`. -/
def IsPeriodicMaximalSolution (ν : ℝ) (u₀ : VelocityField)
    (u : TimeDependentVelocity) (p : TimeDependentPressure) : Prop :=
  ∀ T : ℝ, 0 < T → (T : EReal) < periodicTstar ν u₀ →
    IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p

/-- **Classical (Kato 1972), not formalized here:** positive local existence time. -/
def PeriodicLocalExistence (ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ → (0 : EReal) < periodicTstar ν u₀

/-- A single maximal solution (proved below from `PeriodicVelocityUniqueness`). -/
def PeriodicMaximalSolution (ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure), IsPeriodicMaximalSolution ν u₀ u p

/-- A maximal solution with `periodicTstar = ⊤` solves Statement (B) (proved below outright). -/
def PeriodicGlobalOfTstarTop (ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsPeriodicMaximalSolution ν u₀ u p → periodicTstar ν u₀ = ⊤ →
      ∃ (u' : TimeDependentVelocity) (p' : TimeDependentPressure),
        IsPeriodicSmoothSolution ν u₀ (fun _ _ => 0) u' p'

/-- **Classical (Beale–Kato–Majda 1984), not formalized here.** -/
def PeriodicBKMCriterion (ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsPeriodicMaximalSolution ν u₀ u p →
      ∀ T : ℝ, periodicTstar ν u₀ = (T : EReal) →
        ¬ MeasureTheory.IntegrableOn (fun t => vorticity_sup_norm (vorticity (u t))) (Icc 0 T)

/-- **OPEN:** `‖ω(t)‖_∞` is integrable on every `[0, T]` along the maximal solution. -/
def PeriodicBKMIntegrability (ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsPeriodicMaximalSolution ν u₀ u p →
      ∀ T : ℝ, MeasureTheory.IntegrableOn (fun t => vorticity_sup_norm (vorticity (u t))) (Icc 0 T)

/-- **Classical (energy estimate + Grönwall), named:** two corrected solutions on `[0, T]` from the
same data have the same velocity on `[0, T]`. Reduced to `PeriodicEnergyDifferenceEstimate` in
`Uniqueness.lean`. -/
def PeriodicVelocityUniqueness (ν : ℝ) : Prop :=
  ∀ (u₀ : VelocityField) (T : ℝ) (u v : TimeDependentVelocity) (p q : TimeDependentPressure),
    IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p →
    IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T v q →
    ∀ t ∈ Icc (0 : ℝ) T, u t = v t

/-! ### Basic lemmas -/

section lemmas
variable {ν : ℝ} {u₀ : VelocityField}

lemma slice_mapsTo (T : ℝ) (x : T3) :
    MapsTo (fun s : ℝ => (s, x)) (Icc (0 : ℝ) T) (Icc (0 : ℝ) T ×ˢ (univ : Set T3)) :=
  fun _ hs => ⟨hs, trivial⟩

lemma hasDerivWithinAt_slice {T : ℝ} {u : TimeDependentVelocity}
    (hu : ContDiffOn ℝ ∞ (fun q : ℝ × T3 => u q.1 q.2) (Icc (0 : ℝ) T ×ˢ univ))
    (x : T3) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => u s x) (derivWithin (fun s => u s x) (Icc (0 : ℝ) T) t)
      (Icc (0 : ℝ) T) t := by
  have hc : ContDiffOn ℝ ∞ (fun s : ℝ => u s x) (Icc (0 : ℝ) T) :=
    hu.comp ((contDiff_id.prodMk contDiff_const).contDiffOn) (slice_mapsTo T x)
  exact ((hc.differentiableOn (by simp)) t ht).hasDerivWithinAt

/-- Restriction to a shorter horizon. -/
theorem restrict {T T' : ℝ} {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (h : IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T' u p) (hT : 0 < T) (hTT : T ≤ T') :
    IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p := by
  obtain ⟨-, hpu, hpp, hcu, hcp, heq, hdiv, hinit⟩ := h
  have hsub : Icc (0 : ℝ) T ⊆ Icc 0 T' := Icc_subset_Icc le_rfl hTT
  refine ⟨hT, fun t ht => hpu t (hsub ht), fun t ht => hpp t (hsub ht),
    hcu.mono (prod_mono hsub le_rfl), hcp.mono (prod_mono hsub le_rfl), ?_,
    fun t ht => hdiv t (hsub ht), hinit⟩
  intro t ht x
  have hd := (hasDerivWithinAt_slice hcu x (hsub ht)).mono hsub
  rw [hd.derivWithin ((uniqueDiffOn_Icc hT) t ht)]
  exact heq t (hsub ht) x

/-- Replace `(u, p)` by a pair that agrees with it on `[0, T]`. -/
theorem congr {T : ℝ} {u u' : TimeDependentVelocity} {p p' : TimeDependentPressure}
    (h : IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p)
    (hu : ∀ t ∈ Icc (0 : ℝ) T, u' t = u t) (hp : ∀ t ∈ Icc (0 : ℝ) T, p' t = p t) :
    IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u' p' := by
  obtain ⟨hT, hpu, hpp, hcu, hcp, heq, hdiv, hinit⟩ := h
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  refine ⟨hT, fun t ht => (hu t ht).symm ▸ hpu t ht, fun t ht => (hp t ht).symm ▸ hpp t ht,
    hcu.congr (fun q hq => by simp [hu q.1 hq.1]),
    hcp.congr (fun q hq => by simp [hp q.1 hq.1]), ?_,
    fun t ht x => by rw [hu t ht]; exact hdiv t ht x,
    fun x => by rw [hu 0 h0]; exact hinit x⟩
  intro t ht x
  have hd : derivWithin (fun s => u' s x) (Icc (0 : ℝ) T) t =
      derivWithin (fun s => u s x) (Icc (0 : ℝ) T) t :=
    derivWithin_congr (fun s hs => by simp only [hu s hs]) (by simp only [hu t ht])
  rw [hd, hu t ht, hp t ht]
  exact heq t ht x

/-- Pressure normalised by its value at the origin. -/
def normP (p : TimeDependentPressure) : TimeDependentPressure := fun t x => p t x - p t 0

lemma gradient_sub_const (g : PressureField) (c : ℝ) (x : T3) :
    gradient (fun y => g y - c) x = gradient g x := by
  simp [gradient, fderiv_sub_const]

/-- Normalising the pressure keeps a solution a solution. -/
theorem normP_sol {T : ℝ} {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (h : IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p) :
    IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u (normP p) := by
  obtain ⟨hT, hpu, hpp, hcu, hcp, heq, hdiv, hinit⟩ := h
  refine ⟨hT, hpu, fun t ht y k => by simp [normP, hpp t ht y k], hcu, ?_, ?_, hdiv, hinit⟩
  · have h2 : ContDiffOn ℝ ∞ (fun q : ℝ × T3 => p q.1 0) (Icc (0 : ℝ) T ×ˢ univ) :=
      hcp.comp (contDiff_fst.prodMk contDiff_const).contDiffOn (fun q hq => ⟨hq.1, trivial⟩)
    exact hcp.sub h2
  · intro t ht x
    have : pressureGradient (normP p t) x = pressureGradient (p t) x :=
      gradient_sub_const (p t) (p t 0) x
    rw [this]; exact heq t ht x

/-- **Proved:** two solutions with the same velocity on `[0, T]` have pressures differing by a
function of time only; hence equal normalised pressures. -/
theorem normP_eq_of_velocity_eq {T : ℝ} {u : TimeDependentVelocity} {p q : TimeDependentPressure}
    (hp : IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p)
    (hq : IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u q) :
    ∀ t ∈ Icc (0 : ℝ) T, normP p t = normP q t := by
  intro t ht
  have hdiff : ∀ r : TimeDependentPressure,
      ContDiffOn ℝ ∞ (fun q : ℝ × T3 => r q.1 q.2) (Icc (0 : ℝ) T ×ˢ univ) →
      Differentiable ℝ (r t) := by
    intro r hr
    have hc : ContDiffOn ℝ ∞ (fun y : T3 => r t y) univ :=
      hr.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => ⟨ht, trivial⟩)
    exact fun y => ((contDiffOn_univ.1 hc).differentiable (by simp)) y
  have hdp := hdiff p hp.2.2.2.2.1
  have hdq := hdiff q hq.2.2.2.2.1
  have hgrad : ∀ x, gradient (p t) x = gradient (q t) x := by
    intro x
    have e1 := hp.2.2.2.2.2.1 t ht x
    have e2 := hq.2.2.2.2.2.1 t ht x
    simp only [pressureGradient] at e1 e2
    have := e1.symm.trans e2
    simpa using this
  have hfd : ∀ x, fderiv ℝ (fun y => p t y - q t y) x = 0 := by
    intro x
    rw [fderiv_fun_sub (hdp x) (hdq x)]
    have := congrArg (InnerProductSpace.toDual ℝ T3) (hgrad x)
    simp only [gradient, LinearIsometryEquiv.apply_symm_apply] at this
    rw [this, sub_self]
  have hconst := is_const_of_fderiv_eq_zero (hdp.sub hdq) hfd
  funext x
  have := hconst x 0
  simp only [Pi.sub_apply] at this
  simp only [normP]
  linarith

end lemmas

end PeriodicNSContinuation.Corrected
