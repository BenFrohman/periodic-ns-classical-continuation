/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import Mathlib
import FeffermanClayNS
import TorusFourierNS

/-!
# `PeriodicLocalExistence` from the concrete Galerkin scheme

Everything here is tied by types to the concrete truncated Leray-projected system
`TorusFourierNS.galerkinNSField` (repository `torus-fourier-ns-lemmas`, now a dependency).

Coined names: `fourierCoeffVF`, `IsGalerkinSolutionOn`, `GalerkinUniformBoundNS`,
`PeriodicGalerkinUniformTime`, `PeriodicGalerkinLimit`, `PeriodicDataHs`,
`GalerkinStructurePreserved`, `GalerkinContinuation`.

**Proved:**
* `periodicTstar_pos_of_solution`: a solution on some `T > 0` gives `0 < periodicTstar`.
* `periodicLocalExistence_of_galerkin`: `PeriodicGalerkinUniformTime ν s` and
  `PeriodicGalerkinLimit ν s` imply `PeriodicLocalExistence ν`.
* `periodicGalerkinUniformTime_of`: `PeriodicGalerkinUniformTime ν s` from `PeriodicDataHs s`,
  `GalerkinTransportBound s C`, `GalerkinStructurePreserved ν`, `GalerkinContinuation ν s`
  (energy identity, viscous dissipation and ODE barrier are proved in `GalerkinEnergy`).

**NOT proved (explicit named-Prop inputs):** `PeriodicGalerkinLimit` (compactness, limit,
smoothness, pressure), `PeriodicDataHs` (smooth periodic data have `H^s` Fourier coefficients),
`TorusFourierNS.GalerkinTransportBound` (transport cancellation and commutator estimate),
`GalerkinStructurePreserved` (Hermitian symmetry and `DivergenceFree` along Galerkin solutions on
`[0,T]`), `GalerkinContinuation` (finite-dimensional ODE continuation under an a priori bound).
-/

noncomputable section
open Set FeffermanClayNS NavierStokes3D

namespace PeriodicNSContinuation

/-- Fourier coefficients of a velocity field on the unit cell (coined). -/
def fourierCoeffVF (u₀ : NavierStokes3D.VelocityField) : TorusFourierNS.FField := fun k i =>
  ∫ x in Icc (0 : Fin 3 → ℝ) 1,
    ((u₀ ((EuclideanSpace.equiv (Fin 3) ℝ).symm x) i : ℝ) : ℂ) *
      Complex.exp (-(2 * Real.pi * Complex.I) * ∑ j, ((k j : ℝ) : ℂ) * (x j : ℂ))

/-- `α` solves the `N`-th Galerkin system on `[0,T]` from the truncation of `a`. -/
def IsGalerkinSolutionOn (N : ℕ) (ν : ℝ) (a : TorusFourierNS.FField) (T : ℝ)
    (α : ℝ → TorusFourierNS.GState N) : Prop :=
  α 0 = TorusFourierNS.restrictG N a ∧
    ∀ t ∈ Icc 0 T, HasDerivAt α (TorusFourierNS.galerkinNSField N ν (α t)) t

/-- Uniform-in-`N` `H^s` bound on `[0,T]` for the actual Galerkin solutions from `u₀`. -/
def GalerkinUniformBoundNS (ν s : ℝ) (u₀ : NavierStokes3D.VelocityField) (T : ℝ) : Prop :=
  ∃ M : ℝ, ∀ N : ℕ, ∃ α : ℝ → TorusFourierNS.GState N,
    IsGalerkinSolutionOn N ν (fourierCoeffVF u₀) T α ∧
      ∀ t ∈ Icc 0 T, TorusFourierNS.hsNormField s (TorusFourierNS.extendG (α t)) ≤ M

/-- Uniform existence time for the Galerkin approximants. -/
def PeriodicGalerkinUniformTime (ν s : ℝ) : Prop :=
  ∀ u₀ : NavierStokes3D.VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∃ T : ℝ, 0 < T ∧ GalerkinUniformBoundNS ν s u₀ T

/-- **NOT proved.** Passage to the limit. -/
def PeriodicGalerkinLimit (ν s : ℝ) : Prop :=
  ∀ u₀ : NavierStokes3D.VelocityField, IsPeriodicSmoothInitialData u₀ → ∀ T : ℝ, 0 < T →
    GalerkinUniformBoundNS ν s u₀ T →
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p

/-- **NOT proved.** Smooth periodic data have `H^s` Fourier coefficients. -/
def PeriodicDataHs (s : ℝ) : Prop :=
  ∀ u₀ : NavierStokes3D.VelocityField, IsPeriodicSmoothInitialData u₀ →
    TorusFourierNS.MemHsField s (fourierCoeffVF u₀)

/-- **NOT proved.** Galerkin solutions from smooth periodic data stay Hermitian and
divergence-free. -/
def GalerkinStructurePreserved (ν : ℝ) : Prop :=
  ∀ u₀ : NavierStokes3D.VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∀ (N : ℕ) (T : ℝ) (α : ℝ → TorusFourierNS.GState N),
      IsGalerkinSolutionOn N ν (fourierCoeffVF u₀) T α → ∀ t ∈ Icc 0 T,
        TorusFourierNS.HermitianField (TorusFourierNS.extendG (α t)) ∧
          TorusFourierNS.DivergenceFree (TorusFourierNS.extendG (α t))

/-- **NOT proved.** Finite-dimensional continuation: an a priori bound valid for every solution
on every `[0,T']`, `T' ≤ T`, yields a solution on `[0,T]`. -/
def GalerkinContinuation (ν s : ℝ) : Prop :=
  ∀ (N : ℕ) (a : TorusFourierNS.FField) (T M : ℝ), 0 < T →
    (∀ T' ∈ Icc 0 T, ∀ α : ℝ → TorusFourierNS.GState N, IsGalerkinSolutionOn N ν a T' α →
      ∀ t ∈ Icc 0 T', TorusFourierNS.hsNormField s (TorusFourierNS.extendG (α t)) ≤ M) →
    ∃ α : ℝ → TorusFourierNS.GState N, IsGalerkinSolutionOn N ν a T α

/-- **Proved.** A solution on a positive horizon gives a positive maximal time. -/
theorem periodicTstar_pos_of_solution {ν : ℝ} {u₀ : NavierStokes3D.VelocityField} {T : ℝ}
    (hT : 0 < T)
    (h : ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p) :
    (0 : EReal) < periodicTstar ν u₀ := by
  have hmem : (T : EReal) ∈ periodicExistenceTimes ν u₀ := ⟨T, rfl, h⟩
  exact lt_of_lt_of_le (by exact_mod_cast hT) (le_sSup hmem)

/-- **Conditional assembly** of `PeriodicLocalExistence ν` from the concrete Galerkin inputs. -/
theorem periodicLocalExistence_of_galerkin (ν s : ℝ)
    (hTime : PeriodicGalerkinUniformTime ν s) (hLimit : PeriodicGalerkinLimit ν s) :
    PeriodicLocalExistence ν := by
  intro _ u₀ hu₀
  obtain ⟨T, hT, hB⟩ := hTime u₀ hu₀
  exact periodicTstar_pos_of_solution hT (hLimit u₀ hu₀ T hT hB)

/-- **Conditional.** Uniform Galerkin time from the energy route. -/
theorem periodicGalerkinUniformTime_of {ν s C : ℝ} (hν : 0 ≤ ν) (hC : 0 ≤ C)
    (hData : PeriodicDataHs s) (hTr : TorusFourierNS.GalerkinTransportBound s C)
    (hStr : GalerkinStructurePreserved ν) (hCont : GalerkinContinuation ν s) :
    PeriodicGalerkinUniformTime ν s := by
  intro u₀ hu₀
  set a := fourierCoeffVF u₀
  have ha := hData u₀ hu₀
  set Y := TorusFourierNS.hsNormField s a ^ 2
  have hE := TorusFourierNS.galerkinHsEnergyInequality_of_transport (ν := ν) hν hTr
  set T := TorusFourierNS.barrierTime C Y
  have hT : 0 < T := by
    simp only [T, TorusFourierNS.barrierTime]
    have : 0 ≤ C * (Y + 1) ^ (3/2 : ℝ) := by positivity
    positivity
  have bound : ∀ (N : ℕ) (T' : ℝ), T' ≤ T → ∀ α : ℝ → TorusFourierNS.GState N,
      IsGalerkinSolutionOn N ν a T' α → ∀ t ∈ Icc 0 T',
        TorusFourierNS.hsNormField s (TorusFourierNS.extendG (α t)) ≤ Real.sqrt (Y + 1) := by
    intro N T' hT' α hα t ht
    have h := TorusFourierNS.galerkin_uniform_bound_of_energy hC hE ha hT' hα.1 hα.2
      (hStr u₀ hu₀ N T' α hα) t ht
    exact Real.le_sqrt_of_sq_le h
  refine ⟨T, hT, Real.sqrt (Y + 1), fun N => ?_⟩
  obtain ⟨α, hα⟩ := hCont N a T (Real.sqrt (Y + 1)) hT
    (fun T' hT' α hα => bound N T' hT'.2 α hα)
  exact ⟨α, hα, bound N T le_rfl α hα⟩

end PeriodicNSContinuation
