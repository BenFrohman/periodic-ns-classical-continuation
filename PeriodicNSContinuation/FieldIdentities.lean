/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import FeffermanClayNS

/-!
# Pointwise identities for fields on `T3`

Product rules that put the three terms of the difference energy identity in divergence form:

* `⟨w, (a·∇)w⟩ · 2 = Σₖ ∂ₖ(|w|² aₖ) − |w|² div a`;
* `⟨w, Δw⟩ = Σₖ ∂ₖ⟨w, ∂ₖw⟩ − Σₖ |∂ₖw|²`;
* `⟨w, ∇π⟩ = Σₖ ∂ₖ(π wₖ) − π div w`.
-/

open FeffermanClayNS NavierStokes3D InnerProductSpace
open scoped RealInnerProductSpace

namespace PeriodicNSContinuation.Fields

local notation "e" k => EuclideanSpace.single k (1 : ℝ)

lemma expand (v : T3) : v = ∑ k : Fin 3, v k • (e k) := by
  ext i; fin_cases i <;> simp [Fin.sum_univ_three]

lemma clm_expand {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : T3 →L[ℝ] F) (v : T3) :
    L v = ∑ k : Fin 3, v k • L (e k) := by
  conv_lhs => rw [expand v]
  simp [map_sum, map_smul]

lemma differentiable_comp {a : VelocityField} (ha : Differentiable ℝ a) (i : Fin 3) :
    Differentiable ℝ fun y => a y i :=
  (EuclideanSpace.proj i : T3 →L[ℝ] ℝ).differentiable.comp ha

lemma contDiff_comp {a : VelocityField} {n : WithTop ℕ∞} (ha : ContDiff ℝ n a) (i : Fin 3) :
    ContDiff ℝ n fun y => a y i :=
  (EuclideanSpace.proj i : T3 →L[ℝ] ℝ).contDiff.comp ha

lemma fderiv_comp_apply {a : VelocityField} (ha : Differentiable ℝ a) (i : Fin 3) (x h : T3) :
    fderiv ℝ (fun y => a y i) x h = fderiv ℝ a x h i := by
  have := ((EuclideanSpace.proj i : T3 →L[ℝ] ℝ).hasFDerivAt.comp x (ha x).hasFDerivAt).fderiv
  rw [show (fun y => a y i) = (EuclideanSpace.proj i : T3 →L[ℝ] ℝ) ∘ a from rfl, this]
  rfl

/-- `Σₖ ∂ₖ(g aₖ) = ∇g · a + g div a`. -/
theorem sum_fderiv_mul {g : T3 → ℝ} {a : VelocityField} (hg : Differentiable ℝ g)
    (ha : Differentiable ℝ a) (x : T3) :
    ∑ k : Fin 3, fderiv ℝ (fun y => g y * a y k) x (e k) =
      fderiv ℝ g x (a x) + g x * div a x := by
  have h : ∀ k : Fin 3, fderiv ℝ (fun y => g y * a y k) x (e k) =
      a x k * fderiv ℝ g x (e k) + g x * fderiv ℝ (fun y => a y k) x (e k) := fun k => by
    rw [fderiv_fun_mul (hg x) (differentiable_comp ha k x)]
    simp; ring
  simp only [h, Finset.sum_add_distrib, div, Finset.mul_sum, clm_expand (fderiv ℝ g x) (a x),
    smul_eq_mul]

lemma fderiv_sub_apply {a b : VelocityField} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (x h : T3) : fderiv ℝ (a - b) x h = fderiv ℝ a x h - fderiv ℝ b x h := by
  rw [fderiv_sub (ha x) (hb x)]; rfl

lemma div_sub {a b : VelocityField} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) (x : T3) :
    div (a - b) x = div a x - div b x := by
  simp only [div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [fderiv_comp_apply ha, fderiv_comp_apply hb,
    fderiv_comp_apply (ha.sub hb), fderiv_sub_apply ha hb, PiLp.sub_apply]

lemma laplacian_sub {a b : VelocityField} (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b) (x : T3) :
    laplacian (a - b) x = laplacian a x - laplacian b x := by
  have da := ha.differentiable (by norm_num)
  have db := hb.differentiable (by norm_num)
  have dd : ∀ (c : VelocityField), ContDiff ℝ 2 c → ∀ k : Fin 3,
      Differentiable ℝ fun y => fderiv ℝ c y (e k) := fun c hc k =>
    ((hc.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      (by norm_num)
  simp only [laplacian, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : (fun y => fderiv ℝ (a - b) y (e k)) =
      (fun y => fderiv ℝ a y (e k)) - fun y => fderiv ℝ b y (e k) := by
    funext y; exact fderiv_sub_apply da db y _
  rw [this, fderiv_sub_apply (dd a ha k) (dd b hb k)]

/-- Convective difference: `(a·∇)a − (b·∇)b = ((a−b)·... )`, i.e.
`Da(a) − Db(b) = D(a−b)(a) + Db(a−b)`. -/
lemma convective_sub {a b : VelocityField} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (x : T3) : convective a a x - convective b b x =
      fderiv ℝ (a - b) x (a x) + fderiv ℝ b x ((a - b) x) := by
  simp only [convective, fderiv_sub_apply ha hb, Pi.sub_apply, map_sub]; abel

/-- `2⟨w, Dw(a)⟩ = Σₖ ∂ₖ(|w|² aₖ) − |w|² div a`. -/
theorem two_inner_convective {w a : VelocityField} (hw : Differentiable ℝ w)
    (ha : Differentiable ℝ a) (x : T3) :
    2 * ⟪w x, fderiv ℝ w x (a x)⟫ =
      ∑ k : Fin 3, fderiv ℝ (fun y => ⟪w y, w y⟫ * a y k) x (e k) - ⟪w x, w x⟫ * div a x := by
  have hg : Differentiable ℝ fun y => ⟪w y, w y⟫ := fun y => (hw y).inner ℝ (hw y)
  rw [sum_fderiv_mul hg ha, fderiv_inner_apply ℝ (hw x) (hw x), real_inner_comm (fderiv ℝ w x (a x))]
  ring

/-- `⟨w, Δw⟩ = Σₖ ∂ₖ⟨w, ∂ₖw⟩ − Σₖ |∂ₖw|²`. -/
theorem inner_laplacian {w : VelocityField} (hw : ContDiff ℝ 2 w) (x : T3) :
    ⟪w x, laplacian w x⟫ =
      ∑ k : Fin 3, fderiv ℝ (fun y => ⟪w y, fderiv ℝ w y (e k)⟫) x (e k) -
        ∑ k : Fin 3, ‖fderiv ℝ w x (e k)‖ ^ 2 := by
  have d := hw.differentiable (by norm_num)
  have dd : ∀ k : Fin 3, Differentiable ℝ fun y => fderiv ℝ w y (e k) := fun k =>
    ((hw.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      (by norm_num)
  simp only [laplacian, inner_sum, fderiv_inner_apply ℝ (d x) (dd _ x), Finset.sum_add_distrib,
    real_inner_self_eq_norm_sq]
  ring

/-- `⟨w, ∇π⟩ = Σₖ ∂ₖ(π wₖ) − π div w`. -/
theorem inner_gradient {w : VelocityField} {π : T3 → ℝ} (hw : Differentiable ℝ w)
    (hπ : Differentiable ℝ π) (x : T3) :
    ⟪w x, gradient π x⟫ = ∑ k : Fin 3, fderiv ℝ (fun y => π y * w y k) x (e k) - π x * div w x := by
  rw [sum_fderiv_mul hπ hw, real_inner_comm, gradient, toDual_symm_apply]
  ring

end PeriodicNSContinuation.Fields
