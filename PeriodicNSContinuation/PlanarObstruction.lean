/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.BendingRateTests

/-!
# Planar obstruction: zero bending does not give a uniform `½`-Hölder direction

Coined names (November 2026): `sinShear`, `isPlanarField_sinShear`, `vorticity_sinShear`,
`orthogonalStrain_sinShear`, `sinShear_holder_lower_bound`, `no_uniform_holder_sinShear`.

`sinShear A n` is the velocity `u = -(A/n) cos(n x₁) e₂`, whose vorticity is
`ω = A sin(n x₁) e₃`. Every member has bending identically zero. Yet any `½`-Hölder
constant `K` for `ω/|ω|` on `{|ω| ≥ A/2}` satisfies `2 ≤ K √(π/n)`, so no single `K` works for
all `n`. Pointwise bending control alone therefore cannot imply a uniform Hölder bound. The family
is kinematic: it is not a Navier–Stokes blow-up, and planar flows are global.
-/

open Set FeffermanClayNS NavierStokes3D
open scoped RealInnerProductSpace

namespace PeriodicNSContinuation

/-- Coined. The planar shear `-(A/n) cos(n x₁) e₂`. -/
noncomputable def sinShear (A n : ℝ) : VelocityField :=
  fun y => (-(A / n) * Real.cos (n * y 0)) • EuclideanSpace.single (1 : Fin 3) (1 : ℝ)

private lemma hasFDerivAt_coord0 (n : ℝ) (y : T3) :
    HasFDerivAt (fun z : T3 => n * z 0)
      (n • (EuclideanSpace.proj (0 : Fin 3) : T3 →L[ℝ] ℝ)) y :=
  ((EuclideanSpace.proj (0 : Fin 3) : T3 →L[ℝ] ℝ).hasFDerivAt).const_smul n

private lemma comp_eq (A n : ℝ) (i : Fin 3) :
    (fun y => sinShear A n y i) =
      fun y => (if i = 1 then (-(A / n)) else 0) * Real.cos (n * y 0) := by
  funext y; by_cases h : i = 1 <;> simp [sinShear, EuclideanSpace.single_apply, h]

theorem isPlanarField_sinShear (A n : ℝ) : IsPlanarField (sinShear A n) := by
  refine ⟨?_, ?_, ?_⟩
  · have : Differentiable ℝ (fun y : T3 => -(A / n) * Real.cos (n * y 0)) := fun y =>
      ((hasFDerivAt_coord0 n y).cos.const_mul _).differentiableAt
    exact this.smul_const _
  · intro y s; simp [sinShear, e3v, EuclideanSpace.single_apply]
  · intro y; simp [sinShear, EuclideanSpace.single_apply]

private lemma dc (A n : ℝ) (i j : Fin 3) (x : T3) :
    directionalCoord (sinShear A n) i j x =
      (if i = 1 then (-(A / n)) else 0) * (-(Real.sin (n * x 0)) * (n * (if j = 0 then 1 else 0))) := by
  unfold directionalCoord
  rw [comp_eq]
  have h := ((hasFDerivAt_coord0 n x).cos.const_mul (if i = 1 then (-(A / n)) else 0))
  rw [h.fderiv]
  by_cases hi : i = 1 <;> by_cases hj : j = 0 <;>
    simp [hi, hj] <;> ring

theorem vorticity_sinShear {A n : ℝ} (hn : n ≠ 0) (x : T3) :
    vorticity (sinShear A n) x = (A * Real.sin (n * x 0)) • e3v := by
  rw [vorticity_planar (isPlanarField_sinShear A n) x, dc, dc]
  congr 1; simp; field_simp

/-- **Proved.** Bending is zero everywhere for every member of the family. -/
theorem orthogonalStrain_sinShear (A n : ℝ) (x : T3) :
    orthogonalStrain (sinShear A n) x = 0 :=
  orthogonalStrain_planar (isPlanarField_sinShear A n) x

/-- **Proved.** Any `½`-Hölder constant for the direction on `{|ω| ≥ A/2}` obeys `2 ≤ K √(π/n)`. -/
theorem sinShear_holder_lower_bound {A n K : ℝ} (hA : 0 < A) (hn : 0 < n)
    (hK : ∀ x y : T3, A / 2 ≤ ‖vorticity (sinShear A n) x‖ →
      A / 2 ≤ ‖vorticity (sinShear A n) y‖ →
      ‖‖vorticity (sinShear A n) x‖⁻¹ • vorticity (sinShear A n) x -
        ‖vorticity (sinShear A n) y‖⁻¹ • vorticity (sinShear A n) y‖ ≤ K * Real.sqrt ‖x - y‖) :
    2 ≤ K * Real.sqrt (Real.pi / n) := by
  set x : T3 := EuclideanSpace.single 0 (Real.pi / (2 * n))
  set y : T3 := EuclideanSpace.single 0 (3 * Real.pi / (2 * n))
  have hx : vorticity (sinShear A n) x = A • e3v := by
    rw [vorticity_sinShear hn.ne']
    have : n * x 0 = Real.pi / 2 := by simp [x]; field_simp
    rw [this, Real.sin_pi_div_two, mul_one]
  have hy : vorticity (sinShear A n) y = (-A) • e3v := by
    rw [vorticity_sinShear hn.ne']
    have : n * y 0 = Real.pi / 2 + Real.pi := by simp [y]; field_simp; ring
    rw [this, Real.sin_add_pi, Real.sin_pi_div_two]; ring_nf
  have he : ‖e3v‖ = 1 := by simp [e3v]
  have nx : ‖vorticity (sinShear A n) x‖ = A := by rw [hx, norm_smul, he]; simp [abs_of_pos hA]
  have ny : ‖vorticity (sinShear A n) y‖ = A := by rw [hy, norm_smul, he]; simp [abs_of_pos hA]
  have h := hK x y (by rw [nx]; linarith) (by rw [ny]; linarith)
  rw [nx, ny, hx, hy] at h
  have lhs : ‖A⁻¹ • A • e3v - A⁻¹ • (-A) • e3v‖ = 2 := by
    rw [smul_smul, smul_smul, inv_mul_cancel₀ hA.ne', show A⁻¹ * -A = -1 by field_simp,
      neg_one_smul, sub_neg_eq_add, one_smul, ← two_smul ℝ e3v, norm_smul, he]; simp
  have dist : ‖x - y‖ = Real.pi / n := by
    rw [show x - y = EuclideanSpace.single 0 (Real.pi / (2 * n) - 3 * Real.pi / (2 * n)) by
      ext i; by_cases hi : i = 0 <;> simp [x, y, hi]]
    rw [EuclideanSpace.norm_single, Real.norm_eq_abs,
      show Real.pi / (2 * n) - 3 * Real.pi / (2 * n) = -(Real.pi / n) by field_simp; ring,
      abs_neg, abs_of_pos (div_pos Real.pi_pos hn)]
  rw [lhs, dist] at h; exact h

/-- **Proved.** No single Hölder constant serves the whole zero-bending family `n ≥ 1`. -/
theorem no_uniform_holder_sinShear {A : ℝ} (hA : 0 < A) :
    ¬ ∃ K : ℝ, ∀ n : ℝ, 1 ≤ n → ∀ x y : T3, A / 2 ≤ ‖vorticity (sinShear A n) x‖ →
      A / 2 ≤ ‖vorticity (sinShear A n) y‖ →
      ‖‖vorticity (sinShear A n) x‖⁻¹ • vorticity (sinShear A n) x -
        ‖vorticity (sinShear A n) y‖⁻¹ • vorticity (sinShear A n) y‖ ≤ K * Real.sqrt ‖x - y‖ := by
  rintro ⟨K, hK⟩
  have hK0 : 0 < K := by
    have h := sinShear_holder_lower_bound hA one_pos (hK 1 le_rfl)
    by_contra hc; push_neg at hc
    nlinarith [Real.sqrt_nonneg (Real.pi / 1)]
  set n : ℝ := Real.pi * K ^ 2 + 1
  have hn : 1 ≤ n := by simp only [n]; nlinarith [Real.pi_pos, sq_nonneg K]
  have h := sinShear_holder_lower_bound hA (by linarith) (hK n hn)
  have hlt : Real.pi / n < Real.pi / (Real.pi * K ^ 2) :=
    div_lt_div_of_pos_left Real.pi_pos (by positivity) (by linarith)
  have hs : Real.sqrt (Real.pi / n) < 1 / K := by
    rw [show 1 / K = Real.sqrt (Real.pi / (Real.pi * K ^ 2)) by
      rw [show Real.pi / (Real.pi * K ^ 2) = (1 / K) ^ 2 by field_simp,
        Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_lt_sqrt (by positivity) hlt
  have : K * Real.sqrt (Real.pi / n) < 1 := by
    calc K * Real.sqrt (Real.pi / n) < K * (1 / K) := mul_lt_mul_of_pos_left hs hK0
      _ = 1 := by field_simp
  linarith

end PeriodicNSContinuation
