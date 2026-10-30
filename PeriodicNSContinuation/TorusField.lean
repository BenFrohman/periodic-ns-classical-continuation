/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.TorusIntegral
import FeffermanClayNS

/-!
# Integrals over the unit cell of fields on `T3`

`cellIntegral g = ∫_{[0,1]³} g`, computed with `WeightedEnstrophy.Torus.torusIntegral`, and the
periodic divergence theorem: `∫_{[0,1]³} ∂ₖ φ = 0` for a `C¹`, `ℤ³`-periodic `φ`.
-/

open MeasureTheory Set WeightedEnstrophy.Torus FeffermanClayNS NavierStokes3D

namespace PeriodicNSContinuation.Torus

/-- The point `(a, b, c)` of `T3`. -/
noncomputable def toT3 (a b c : ℝ) : T3 := (EuclideanSpace.equiv (Fin 3) ℝ).symm ![a, b, c]

@[simp] lemma toT3_apply (a b c : ℝ) (i : Fin 3) : toT3 a b c i = ![a, b, c] i := rfl

lemma continuous_toT3 : Continuous fun q : E => toT3 q.2.1 q.2.2.1 q.2.2.2 := by
  refine (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp (continuous_pi fun i => ?_)
  fin_cases i <;> simp <;> fun_prop

/-- Lift of a field on `T3` to the coordinates `(t, a, b, c)` used by `torusIntegral`. -/
noncomputable def lift {α : Type*} (g : T3 → α) : E → α := fun q => g (toT3 q.2.1 q.2.2.1 q.2.2.2)

lemma continuous_lift {α : Type*} [TopologicalSpace α] {g : T3 → α} (hg : Continuous g) :
    Continuous (lift g) := hg.comp continuous_toT3

/-- `∫_{[0,1]³} g`. -/
noncomputable def cellIntegral (g : T3 → ℝ) : ℝ := torusIntegral (lift g) 0

lemma toT3_shift0 (a b c x : ℝ) : toT3 x b c = toT3 a b c + (x - a) • EuclideanSpace.single 0 1 := by
  ext i; fin_cases i <;> simp
lemma toT3_shift1 (a b c x : ℝ) : toT3 a x c = toT3 a b c + (x - b) • EuclideanSpace.single 1 1 := by
  ext i; fin_cases i <;> simp
lemma toT3_shift2 (a b c x : ℝ) : toT3 a b x = toT3 a b c + (x - c) • EuclideanSpace.single 2 1 := by
  ext i; fin_cases i <;> simp

lemma hasDerivAt_line {φ : T3 → ℝ} (hφ : Differentiable ℝ φ) (p : T3) (k : Fin 3) (a₀ x : ℝ) :
    HasDerivAt (fun y : ℝ => φ (p + (y - a₀) • EuclideanSpace.single k (1 : ℝ)))
      (fderiv ℝ φ (p + (x - a₀) • EuclideanSpace.single k (1 : ℝ)) (EuclideanSpace.single k 1)) x := by
  have hl : HasDerivAt (fun y : ℝ => p + (y - a₀) • EuclideanSpace.single k (1 : ℝ))
      (EuclideanSpace.single k 1) x := by
    simpa using (((hasDerivAt_id x).sub_const a₀).smul_const
      (EuclideanSpace.single k (1 : ℝ))).const_add p
  exact (hφ _).hasFDerivAt.comp_hasDerivAt x hl

/-- **Periodic divergence theorem on the unit cell.** -/
theorem cellIntegral_fderiv_eq_zero {φ : T3 → ℝ} (hφ : ContDiff ℝ 1 φ) (hper : IsZ3Periodic φ)
    (k : Fin 3) : cellIntegral (fun x => fderiv ℝ φ x (EuclideanSpace.single k 1)) = 0 := by
  have hd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hc : Continuous fun x => fderiv ℝ φ x (EuclideanSpace.single k 1) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hu := (isZ3Periodic_iff_unit_shifts φ).1 hper
  unfold cellIntegral
  fin_cases k
  · refine torusIntegral_deriv_a (f := lift φ) (continuous_lift hd.continuous)
      (continuous_lift hc) (fun t a b c => ?_) (fun t a b c => ?_) 0
    · have := hasDerivAt_line hd (toT3 a b c) 0 a a
      simp only [sub_self, zero_smul, add_zero] at this
      refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
      simp [lift, ← toT3_shift0]
    · have := hu (toT3 a b c) 0
      simp only [lift]
      rw [← this]; congr 1; ext i; fin_cases i <;> simp [stdBasisVec]
  · refine torusIntegral_deriv_b (f := lift φ) (continuous_lift hd.continuous)
      (continuous_lift hc) (fun t a b c => ?_) (fun t a b c => ?_) 0
    · have := hasDerivAt_line hd (toT3 a b c) 1 b b
      simp only [sub_self, zero_smul, add_zero] at this
      refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
      simp [lift, ← toT3_shift1]
    · have := hu (toT3 a b c) 1
      simp only [lift]
      rw [← this]; congr 1; ext i; fin_cases i <;> simp [stdBasisVec]
  · refine torusIntegral_deriv_c (f := lift φ)
      (continuous_lift hc) (fun t a b c => ?_) (fun t a b c => ?_) 0
    · have := hasDerivAt_line hd (toT3 a b c) 2 c c
      simp only [sub_self, zero_smul, add_zero] at this
      refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
      simp [lift, ← toT3_shift2]
    · have := hu (toT3 a b c) 2
      simp only [lift]
      rw [← this]; congr 1; ext i; fin_cases i <;> simp [stdBasisVec]

/-! ### Linearity and order -/

lemma integral01_add {φ ψ : ℝ → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ) :
    ∫ x in (0:ℝ)..1, (φ x + ψ x) = (∫ x in (0:ℝ)..1, φ x) + ∫ x in (0:ℝ)..1, ψ x :=
  intervalIntegral.integral_add (hφ.intervalIntegrable 0 1) (hψ.intervalIntegrable 0 1)

theorem torusIntegral_add' {f g : E → ℝ} (hf : Continuous f) (hg : Continuous g) (t : ℝ) :
    torusIntegral (fun q => f q + g q) t = torusIntegral f t + torusIntegral g t := by
  have c3f := cont_i3 hf; have c3g := cont_i3 hg
  have c2f := cont_i2 hf; have c2g := cont_i2 hg
  have h3 : ∀ q, i3 (fun q => f q + g q) q = i3 f q + i3 g q := fun q =>
    integral01_add (by fun_prop) (by fun_prop)
  have h2 : ∀ q, i2 (fun q => f q + g q) q = i2 f q + i2 g q := fun q => by
    simp only [WeightedEnstrophy.Torus.i2, h3]; exact integral01_add (by fun_prop) (by fun_prop)
  simp only [WeightedEnstrophy.Torus.torusIntegral, h2]; exact integral01_add (by fun_prop) (by fun_prop)

theorem torusIntegral_const_mul (r : ℝ) (f : E → ℝ) (t : ℝ) :
    torusIntegral (fun q => r * f q) t = r * torusIntegral f t := by
  simp [WeightedEnstrophy.Torus.torusIntegral, WeightedEnstrophy.Torus.i2,
    WeightedEnstrophy.Torus.i3, intervalIntegral.integral_const_mul]

lemma cellIntegral_add {g h : T3 → ℝ} (hg : Continuous g) (hh : Continuous h) :
    cellIntegral (fun x => g x + h x) = cellIntegral g + cellIntegral h :=
  torusIntegral_add' (continuous_lift hg) (continuous_lift hh) 0

lemma cellIntegral_const_mul (r : ℝ) (g : T3 → ℝ) :
    cellIntegral (fun x => r * g x) = r * cellIntegral g :=
  torusIntegral_const_mul r (lift g) 0

lemma cellIntegral_sum {g : Fin 3 → T3 → ℝ} (hg : ∀ k, Continuous (g k)) :
    cellIntegral (fun x => ∑ k, g k x) = ∑ k, cellIntegral (g k) := by
  simp only [Fin.sum_univ_three]
  rw [cellIntegral_add (by fun_prop) (hg 2), cellIntegral_add (hg 0) (hg 1)]

/-- Integral of a periodic divergence vanishes. -/
theorem cellIntegral_sum_fderiv_eq_zero {φ : Fin 3 → T3 → ℝ} (hφ : ∀ k, ContDiff ℝ 1 (φ k))
    (hper : ∀ k, IsZ3Periodic (φ k)) :
    cellIntegral (fun x => ∑ k, fderiv ℝ (φ k) x (EuclideanSpace.single k 1)) = 0 := by
  rw [cellIntegral_sum fun k => ((hφ k).continuous_fderiv one_ne_zero).clm_apply continuous_const]
  simp [cellIntegral_fderiv_eq_zero (hφ _) (hper _)]


end PeriodicNSContinuation.Torus
