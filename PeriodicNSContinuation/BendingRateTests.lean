/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.BendingRate

/-!
# Tests of the hidden property `PeriodicBendingRateHiddenProperty`

* `orthogonalStrain_planar` — **proved**: for a differentiable planar field
  `v = (v₁(x₁,x₂), v₂(x₁,x₂), 0)` the orthogonal strain `(I − t⊗t) S t` vanishes identically.
  So 2D flows satisfy the bending bound with `C = 0`.
* `bendingRateHiddenProperty_of_noFiniteLifespan` — **proved**: if no smooth periodic datum
  has a finite maximal lifespan, the hidden property holds (vacuously). Every quantifier in it
  ranges over solutions with `periodicTstar ν u₀ = T` finite.
* `orthogonalStrainToDirectionHolder_of_directionRegularity` — **proved**: the second conjunct
  is implied by `PeriodicDirectionRegularity` alone, without using the strain bound.
Consequently no global explicit flow (shear, Beltrami, 2D) can refute the property: it is a
statement about hypothetical blow-up solutions only. Nothing here proves it.
-/

noncomputable section
open Set FeffermanClayNS NavierStokes3D
open scoped RealInnerProductSpace

namespace PeriodicNSContinuation

/-- Coined. `e₃`. -/
abbrev e3v : T3 := EuclideanSpace.single 2 1

/-- Coined. A field constant along `e₃` has zero derivative in direction `e₃`. -/
theorem fderiv_apply_e3_of_inv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : T3 → F) (hf : ∀ y (s : ℝ), f (y + s • e3v) = f y) (x : T3) :
    fderiv ℝ f x e3v = 0 := by
  by_cases hd : DifferentiableAt ℝ f x
  · have hl : HasDerivAt (fun s : ℝ => x + s • e3v) e3v 0 := by
      have h0 : HasDerivAt (fun s : ℝ => s • e3v) ((1:ℝ) • e3v) 0 :=
        (hasDerivAt_id (0:ℝ)).smul_const e3v
      simpa using h0.const_add x
    have hd' : HasFDerivAt f (fderiv ℝ f x) (x + (0:ℝ) • e3v) := by simpa using hd.hasFDerivAt
    have h1 := hd'.comp_hasDerivAt (0:ℝ) hl
    have h2 : HasDerivAt (fun s : ℝ => f (x + s • e3v)) 0 0 := by
      have : (fun s : ℝ => f (x + s • e3v)) = fun _ => f x := funext fun s => hf x s
      rw [this]; exact hasDerivAt_const _ _
    exact h1.unique h2
  · simp [fderiv_zero_of_not_differentiableAt hd]

/-- Coined. Planar field: invariant along `e₃`, zero third component. -/
def IsPlanarField (v : VelocityField) : Prop :=
  Differentiable ℝ v ∧ (∀ y (s : ℝ), v (y + s • e3v) = v y) ∧ ∀ y, v y 2 = 0

/-- **Proved.** `S e₃ = 0` for a planar field. -/
theorem strainAt_e3_planar {v : VelocityField} (hv : IsPlanarField v) (x : T3) :
    strainAt v x e3v = 0 := by
  obtain ⟨hd, hinv, h3⟩ := hv
  have hA : fderiv ℝ v x e3v = 0 := fderiv_apply_e3_of_inv v hinv x
  have hB : ContinuousLinearMap.adjoint (fderiv ℝ v x) e3v = 0 := by
    apply ext_inner_left ℝ
    intro w
    rw [ContinuousLinearMap.adjoint_inner_right, inner_zero_right]
    have hc : (fderiv ℝ v x w) 2 = fderiv ℝ (fun y => v y 2) x w := by
      have h := ((EuclideanSpace.proj (2 : Fin 3) : T3 →L[ℝ] ℝ).hasFDerivAt).comp x
        (hd x).hasFDerivAt
      rw [show (fun y => v y 2) = (EuclideanSpace.proj (2 : Fin 3) : T3 →L[ℝ] ℝ) ∘ v from rfl,
        h.fderiv]
      rfl
    have h0 : (fun y => v y 2) = fun _ => (0:ℝ) := funext h3
    rw [h0, fderiv_fun_const] at hc
    show ⟪fderiv ℝ v x w, EuclideanSpace.single (2:Fin 3) (1:ℝ)⟫ = 0
    simp [PiLp.inner_apply, Fin.sum_univ_three, EuclideanSpace.single_apply, hc]
  simp [strainAt, hA, hB]

/-- **Proved.** For a planar field the vorticity is a multiple of `e₃`. -/
theorem vorticity_planar {v : VelocityField} (hv : IsPlanarField v) (x : T3) :
    vorticity v x = (directionalCoord v 1 0 x - directionalCoord v 0 1 x) • e3v := by
  obtain ⟨hd, hinv, h3⟩ := hv
  have hc (i : Fin 3) : directionalCoord v i 2 x = 0 :=
    fderiv_apply_e3_of_inv (fun y => v y i) (fun y s => by simp only [hinv]) x
  have h0 : (fun y => v y 2) = fun _ => (0:ℝ) := funext h3
  have hz (j : Fin 3) : directionalCoord v 2 j x = 0 := by
    simp [directionalCoord, h0]
  show curl v x = _
  simp only [curl, hc, hz, sub_self]
  ext i
  fin_cases i <;> simp [EuclideanSpace.single_apply]

/-- **Proved.** Planar (2D) fields have zero orthogonal strain everywhere. -/
theorem orthogonalStrain_planar {v : VelocityField} (hv : IsPlanarField v) (x : T3) :
    orthogonalStrain v x = 0 := by
  have hS := strainAt_e3_planar hv x
  rw [orthogonalStrain, vortDir, vorticity_planar hv x, smul_smul, map_smul, hS, smul_zero]
  simp [perpPart]

/-- **Proved.** Vacuity: with no finite maximal lifespan, the hidden property holds trivially. -/
theorem bendingRateHiddenProperty_of_noFiniteLifespan {ν : ℝ}
    (h : ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
      ∀ T : ℝ, periodicTstar ν u₀ ≠ (T : EReal)) :
    PeriodicBendingRateHiddenProperty ν :=
  ⟨fun _ u₀ hu₀ _ _ _ T hT => absurd hT (h u₀ hu₀ T),
   fun _ u₀ hu₀ _ _ _ T hT => absurd hT (h u₀ hu₀ T)⟩

/-- **Proved.** The second conjunct follows from `PeriodicDirectionRegularity` alone. -/
theorem orthogonalStrainToDirectionHolder_of_directionRegularity {ν : ℝ}
    (h : PeriodicDirectionRegularity ν) : OrthogonalStrainToDirectionHolder ν :=
  fun hν u₀ hu₀ u p hm T hT _ => h hν u₀ hu₀ u p hm T hT

end PeriodicNSContinuation
