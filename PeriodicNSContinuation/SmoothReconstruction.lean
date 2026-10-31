/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.PDE
import PeriodicNSContinuation.HigherRegularity

/-!
# Reconstruction of a smooth periodic solution from the Galerkin limit (names coined)

**Proved:** `fourierSeriesVelocitySmooth_of_modeCont` and `periodicPressureRecovery_of_modeCont`:
the conclusions of `FourierSeriesVelocitySmooth` and `PeriodicPressureRecovery` for a smooth
Fourier solution whose modes are additionally continuous in time on `[0,T]`.

**Proved:** `periodicGalerkinLimit_of_nonneg (0 ≤ ν) (5/2 < s) : PeriodicGalerkinLimit ν s`, with no
hypothesis Props: the Galerkin limit inherits the equi-Lipschitz bound, so its modes are continuous.

**Not proved:** `FourierSeriesVelocitySmooth ν` and `PeriodicPressureRecovery ν` as stated, i.e.
without mode continuity. The integral equation alone does not force continuity (a non-integrable
integrand makes the interval integral `0`), so these remain open as stated.
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D
open scoped ContDiff

namespace PeriodicNSContinuation

/-- Continuity in time of every Fourier mode on `[0,T]` (coined). -/
def ModeContinuous (T : ℝ) (a : ℝ → TorusFourierNS.FField) : Prop :=
  ∀ k i, ContinuousOn (fun t => a t k i) (Icc 0 T)

lemma IsSmoothFourierSolutionOn.curveHyp {ν T : ℝ} {u₀ : NavierStokes3D.VelocityField}
    {a : ℝ → TorusFourierNS.FField} (ha : IsSmoothFourierSolutionOn ν u₀ T a)
    (hm : ModeContinuous T a) : CurveHyp ν T a :=
  ⟨ha.2.1, ha.2.2.2, hm⟩

/-- **Proved.** The conclusion of `FourierSeriesVelocitySmooth`, given mode continuity. -/
theorem fourierSeriesVelocitySmooth_of_modeCont {ν T : ℝ} {u₀ : NavierStokes3D.VelocityField}
    (hT : 0 < T) {a : ℝ → TorusFourierNS.FField} (ha : IsSmoothFourierSolutionOn ν u₀ T a)
    (hm : ModeContinuous T a) :
    ContDiffOn ℝ ∞ (fun q : ℝ × T3 => seriesVelocity a q.1 q.2) (Icc (0 : ℝ) T ×ˢ univ) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x : T3, div (seriesVelocity a t) x = 0) :=
  ⟨(ha.curveHyp hm).contDiffOn_seriesVelocity hT,
   fun _ ht x => div_seriesVelocity ha.2.1 ht (ha.2.2.1 _ ht).2 x⟩

/-- **Proved.** The conclusion of `PeriodicPressureRecovery`, given mode continuity. -/
theorem periodicPressureRecovery_of_modeCont {ν T : ℝ} {u₀ : NavierStokes3D.VelocityField}
    (hT : 0 < T) {a : ℝ → TorusFourierNS.FField} (ha : IsSmoothFourierSolutionOn ν u₀ T a)
    (hm : ModeContinuous T a) :
    ContDiffOn ℝ ∞ (fun q : ℝ × T3 => seriesPressure a q.1 q.2) (Icc (0 : ℝ) T ×ˢ univ) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x : T3,
        derivWithin (fun s => seriesVelocity a s x) (Icc (0 : ℝ) T) t +
            convective (seriesVelocity a t) (seriesVelocity a t) x =
          ν • laplacian (seriesVelocity a t) x - pressureGradient (seriesPressure a t) x +
            (fun _ _ => (0 : EuclideanSpace ℝ (Fin 3))) t x) :=
  ⟨(ha.curveHyp hm).contDiffOn_seriesPressure hT,
   fun _ ht x => (ha.curveHyp hm).momentum hT (fun t ht => (ha.2.2.1 t ht).1) ht x⟩

/-- **Proved.** Mode-wise limits of equi-Lipschitz curves are continuous. -/
lemma modeContinuous_of_tendsto {T : ℝ} {x : ℕ → ℝ → TorusFourierNS.FField}
    {a : ℝ → TorusFourierNS.FField} (L : TorusFourierNS.Mode → ℝ)
    (hL : ∀ n, ∀ t₁ ∈ Icc 0 T, ∀ t₂ ∈ Icc 0 T, ∀ k i, ‖x n t₁ k i - x n t₂ k i‖ ≤ L k * |t₁ - t₂|)
    (hc : ∀ t ∈ Icc 0 T, ∀ k i, Tendsto (fun n => x n t k i) atTop (𝓝 (a t k i))) :
    ModeContinuous T a := by
  intro k i
  have hLip : LipschitzOnWith (L k).toNNReal (fun t => a t k i) (Icc 0 T) :=
    LipschitzOnWith.of_dist_le_mul fun t₁ h₁ t₂ h₂ => by
      rw [dist_eq_norm, Real.dist_eq]
      refine (le_of_tendsto' (((hc t₁ h₁ k i).sub (hc t₂ h₂ k i)).norm)
        fun n => hL n t₁ h₁ t₂ h₂ k i).trans ?_
      exact mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (abs_nonneg _)
  exact hLip.continuousOn

/-- **Proved (`ν ≥ 0`, `5/2 < s`), no hypothesis Props.** -/
theorem periodicGalerkinLimit_of_nonneg {ν s : ℝ} (hν : 0 ≤ ν) (hs : 5 / 2 < s) :
    PeriodicGalerkinLimit ν s := by
  have hs2 : 2 < s := by linarith
  intro u₀ hu₀ T hT ⟨M, hM⟩
  choose α hαs hαb using hM
  obtain ⟨L, hLip⟩ := galerkinModeEquiLipschitz hs2 u₀ hu₀ T hT M α hαs hαb
  obtain ⟨φ, hφ, a, hconv⟩ :=
    galerkinModeConvergence_of (galerkinModeEquiLipschitz hs2) u₀ hu₀ T hT M α hαs hαb
  have hstr := galerkinStructurePreserved_of ν periodicDataDivFree u₀ hu₀
  have h0 : a 0 = fourierCoeffVF u₀ := limit_initial hαs hφ (hconv 0 ⟨le_rfl, hT.le⟩)
  have heq := galerkinLimitEquation hs2 u₀ hu₀ T hT M α hαs hαb φ hφ a hconv
  have hstrA : ∀ t ∈ Icc 0 T, TorusFourierNS.HermitianField (a t) ∧
      TorusFourierNS.DivergenceFree (a t) := fun t ht =>
    ⟨hermitian_of_tendsto (fun n => (hstr (φ n) T (α (φ n)) (hαs (φ n)) t ht).1) (hconv t ht),
     divergenceFree_of_tendsto (fun n => (hstr (φ n) T (α (φ n)) (hαs (φ n)) t ht).2) (hconv t ht)⟩
  have hsm : IsSmoothFourierSolutionOn ν u₀ T a :=
    ⟨h0, fun s' => hs_bound_of_galerkin (N := φ) (α := fun n => α (φ n)) hν hs hu₀ hT
      (fun n => (hαs (φ n)).1) (fun n => (hαs (φ n)).2)
      (fun n => hstr (φ n) T (α (φ n)) (hαs (φ n))) (fun n => hαb (φ n)) hconv s', hstrA, heq⟩
  have hm : ModeContinuous T a :=
    modeContinuous_of_tendsto (x := fun n t => TorusFourierNS.extendG (α (φ n) t)) L
      (fun n => hLip (φ n)) hconv
  obtain ⟨hVc, hVd⟩ := fourierSeriesVelocitySmooth_of_modeCont hT hsm hm
  obtain ⟨hPc, hPe⟩ := periodicPressureRecovery_of_modeCont hT hsm hm
  exact ⟨seriesVelocity a, seriesPressure a, hT, fun t _ => seriesVelocity_periodic a t,
    fun t _ => seriesPressure_periodic a t, hVc, hPc, hPe, hVd, seriesVelocity_zero hu₀ h0⟩

end PeriodicNSContinuation
