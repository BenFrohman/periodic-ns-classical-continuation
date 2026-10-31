/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.LowFreqKernel

/-!
# Fourier-side Biot–Savart (step 1 toward `PeriodicLowFreqVorticityBound`)

For smooth periodic divergence-free `v` and `k ≠ 0`:
`gradCoeff v k i j = -k_j (k × ω̂_k)_i / |k|²`, where `ω̂` are the unit-cell coefficients of
`vorticity v`. All declaration names here are coined (see README).
-/

noncomputable section
open Set MeasureTheory FeffermanClayNS NavierStokes3D TorusFourierNS

namespace PeriodicNSContinuation

local notation "Eq3" => EuclideanSpace.equiv (Fin 3) ℝ

/-- Coined. Complex cross product `k × u` with real `k`. -/
def crossC (k : Fin 3 → ℝ) (u : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![(k 1 : ℂ) * u 2 - (k 2 : ℂ) * u 1, (k 2 : ℂ) * u 0 - (k 0 : ℂ) * u 2,
    (k 0 : ℂ) * u 1 - (k 1 : ℂ) * u 0]

/-- Coined. Unit-cell Fourier coefficient of component `a` of `vorticity v`. -/
def vortCoeff (v : VelocityField) (k : Mode) (a : Fin 3) : ℂ :=
  cubeCoeff (liftR fun y => vorticity v y a) k

lemma vort_comp (v : VelocityField) (y : T3) :
    vorticity v y 0 = pdR 1 (fun z => v z 2) y - pdR 2 (fun z => v z 1) y ∧
    vorticity v y 1 = pdR 2 (fun z => v z 0) y - pdR 0 (fun z => v z 2) y ∧
    vorticity v y 2 = pdR 0 (fun z => v z 1) y - pdR 1 (fun z => v z 0) y := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [vorticity, curl, directionalCoord, pdR]

/-- **Proved.** `ω̂_k = 2πi k × v̂_k`. -/
lemma vortCoeff_eq {v : VelocityField} (hv : IsPeriodicSmoothInitialData v) (k : Mode)
    (a : Fin 3) :
    vortCoeff v k a = 2 * Real.pi * Complex.I * crossC (kvec k) (fourierCoeffVF v k) a := by
  have hφ : ∀ l, PerR (fun y => v y l) := fun l => perR_coord hv.1 hv.2.2 l
  have key : ∀ p q r s : Fin 3, (∀ y, vorticity v y a =
      pdR p (fun z => v z q) y - pdR r (fun z => v z s) y) →
      vortCoeff v k a = 2 * Real.pi * Complex.I *
        (((k p : ℝ) : ℂ) * fourierCoeffVF v k q - ((k r : ℝ) : ℂ) * fourierCoeffVF v k s) := by
    intro p q r s h
    have e : liftR (fun y => vorticity v y a) =
        fun x => liftR (pdR p (fun z => v z q)) x - liftR (pdR r (fun z => v z s)) x := by
      funext x; simp only [liftR, h]; push_cast; rfl
    rw [vortCoeff, e, cubeCoeff_sub' ((hφ q).pdR p).continuous_liftR
      ((hφ s).pdR r).continuous_liftR, cubeCoeff_pdR (hφ q), cubeCoeff_pdR (hφ s),
      fourierCoeffVF_eq_cubeCoeff, fourierCoeffVF_eq_cubeCoeff, compC_eq_liftR,
      compC_eq_liftR]; ring
  fin_cases a
  · rw [key 1 2 2 1 fun y => (vort_comp v y).1]; simp [crossC, kvec]
  · rw [key 2 0 0 2 fun y => (vort_comp v y).2.1]; simp [crossC, kvec]
  · rw [key 0 1 1 0 fun y => (vort_comp v y).2.2]; simp [crossC, kvec]

/-- **Proved.** Fourier-side Biot–Savart: for `k ≠ 0`,
`gradCoeff v k i j = -k_j (k × ω̂_k)_i / |k|²`. -/
theorem gradCoeff_eq_vort {v : VelocityField} (hv : IsPeriodicSmoothInitialData v) {k : Mode}
    (hk : k ≠ 0) (i j : Fin 3) :
    gradCoeff v k i j = -((k j : ℝ) : ℂ) * crossC (kvec k) (vortCoeff v k) i /
      (ksq (kvec k) : ℂ) := by
  have hdiv := periodicDataDivFree v hv k
  have hks : (ksq (kvec k) : ℂ) ≠ 0 := by
    norm_cast
    intro h0; apply hk; funext l
    have : ∀ m ∈ (Finset.univ : Finset (Fin 3)), kvec k m ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun m _ => sq_nonneg _).1 h0
    have := this l (Finset.mem_univ _)
    simpa [kvec] using this
  have hv' : ∀ a, vortCoeff v k a = _ := vortCoeff_eq hv k
  simp only [dot, Fin.sum_univ_three] at hdiv
  simp only [ksq, Fin.sum_univ_three] at hks ⊢
  rw [eq_div_iff hks]
  simp only [gradCoeff, crossC, hv', kvec]
  fin_cases i <;> simp [kvec] at hdiv ⊢
  · linear_combination (2 * Real.pi * Complex.I * (k j : ℂ) * (k 0 : ℂ)) * hdiv
  · linear_combination (2 * Real.pi * Complex.I * (k j : ℂ) * (k 1 : ℂ)) * hdiv
  · linear_combination (2 * Real.pi * Complex.I * (k j : ℂ) * (k 2 : ℂ)) * hdiv

/-- **Proved.** The zero mode does not enter the gradient. -/
lemma gradCoeff_zero (v : VelocityField) (i j : Fin 3) : gradCoeff v 0 i j = 0 := by
  simp [gradCoeff]
