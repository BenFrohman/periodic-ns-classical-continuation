/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.PhysicalCommutator

/-!
# Kato–Ponce toolkit on the unit cell

Calculus for smooth periodic scalar fields (`PerR`) integrated over the unit cell `[0,1]³`:
closure lemmas, Leibniz rule, integration by parts, and a Gagliardo–Nirenberg inequality.
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D TorusFourierNS
open scoped ContDiff

namespace PeriodicNSContinuation

local notation "Eq3" => EuclideanSpace.equiv (Fin 3) ℝ

/-- Coined. Integral of a scalar field over the unit cell `[0,1]³`. -/
def cellI (φ : T3 → ℝ) : ℝ := ∫ x in Icc (0 : Fin 3 → ℝ) 1, φ ((Eq3).symm x)

lemma PerR.cont {φ : T3 → ℝ} (h : PerR φ) : Continuous φ := h.1.continuous

lemma PerR.mul {φ ψ : T3 → ℝ} (h : PerR φ) (h' : PerR ψ) : PerR (fun y => φ y * ψ y) :=
  ⟨h.1.mul h'.1, fun x j => by simp only [h.2 x j, h'.2 x j]⟩

lemma PerR.add {φ ψ : T3 → ℝ} (h : PerR φ) (h' : PerR ψ) : PerR (fun y => φ y + ψ y) :=
  ⟨h.1.add h'.1, fun x j => by simp only [h.2 x j, h'.2 x j]⟩

lemma PerR.const_mul {φ : T3 → ℝ} (h : PerR φ) (c : ℝ) : PerR (fun y => c * φ y) :=
  ⟨contDiff_const.mul h.1, fun x j => by simp only [h.2 x j]⟩

lemma PerR.sum {ι : Type*} (s : Finset ι) {φ : ι → T3 → ℝ} (h : ∀ i, PerR (φ i)) :
    PerR (fun y => ∑ i ∈ s, φ i y) :=
  ⟨ContDiff.sum fun i _ => (h i).1, fun x j => by simp only [(h _).2 x j]⟩

lemma integrableOn_cell {φ : T3 → ℝ} (h : Continuous φ) :
    IntegrableOn (fun x => φ ((Eq3).symm x)) (Icc (0 : Fin 3 → ℝ) 1) :=
  (h.comp (Eq3).symm.continuous).continuousOn.integrableOn_compact isCompact_Icc

lemma cellI_add {φ ψ : T3 → ℝ} (h : Continuous φ) (h' : Continuous ψ) :
    cellI (fun y => φ y + ψ y) = cellI φ + cellI ψ :=
  integral_add (integrableOn_cell h) (integrableOn_cell h')

lemma cellI_const_mul (φ : T3 → ℝ) (c : ℝ) : cellI (fun y => c * φ y) = c * cellI φ :=
  integral_const_mul c _

lemma cellI_neg (φ : T3 → ℝ) : cellI (fun y => -φ y) = -cellI φ := integral_neg _

lemma cellI_sum {ι : Type*} (s : Finset ι) {φ : ι → T3 → ℝ} (h : ∀ i, Continuous (φ i)) :
    cellI (fun y => ∑ i ∈ s, φ i y) = ∑ i ∈ s, cellI (φ i) :=
  integral_finset_sum s fun i _ => integrableOn_cell (h i)

lemma cellI_mono {φ ψ : T3 → ℝ} (h : Continuous φ) (h' : Continuous ψ) (hle : ∀ y, φ y ≤ ψ y) :
    cellI φ ≤ cellI ψ :=
  setIntegral_mono (integrableOn_cell h) (integrableOn_cell h') fun x => hle _

lemma cellI_nonneg {φ : T3 → ℝ} (hle : ∀ y, 0 ≤ φ y) : 0 ≤ cellI φ :=
  setIntegral_nonneg measurableSet_Icc fun x _ => hle _

lemma cellI_pdR {φ : T3 → ℝ} (h : PerR φ) (j : Fin 3) : cellI (pdR j φ) = 0 := by
  have h0 := integral_pdC_eq_zero j (liftR φ) ((liftR_contDiff h.1).of_le (by simp))
    (liftR_add_single h j)
  have e : (fun x => pdC j (liftR φ) x) = fun x => ((pdR j φ ((Eq3).symm x) : ℝ) : ℂ) :=
    funext fun x => pdC_liftR (h.1.differentiable (by simp)) j x
  rw [e, integral_complex_ofReal] at h0
  exact_mod_cast h0

/-- Leibniz rule for `pdR`. -/
lemma pdR_mul {φ ψ : T3 → ℝ} (h : Differentiable ℝ φ) (h' : Differentiable ℝ ψ) (j : Fin 3) :
    pdR j (fun y => φ y * ψ y) = fun y => pdR j φ y * ψ y + φ y * pdR j ψ y := by
  funext y
  show fderiv ℝ (φ * ψ) y _ = _
  rw [((h y).hasFDerivAt.mul (h' y).hasFDerivAt).fderiv]
  simp [ContinuousLinearMap.add_apply, smul_eq_mul, pdR]; ring

lemma pdR_add {φ ψ : T3 → ℝ} (h : Differentiable ℝ φ) (h' : Differentiable ℝ ψ) (j : Fin 3) :
    pdR j (fun y => φ y + ψ y) = fun y => pdR j φ y + pdR j ψ y := by
  funext y; show fderiv ℝ (φ + ψ) y _ = _
  rw [((h y).hasFDerivAt.add (h' y).hasFDerivAt).fderiv]; rfl

lemma pdR_const_mul {φ : T3 → ℝ} (h : Differentiable ℝ φ) (c : ℝ) (j : Fin 3) :
    pdR j (fun y => c * φ y) = fun y => c * pdR j φ y := by
  funext y; simp only [pdR]; rw [((h y).hasFDerivAt.const_mul c).fderiv]; rfl

lemma pdR_sum {ι : Type*} (s : Finset ι) {φ : ι → T3 → ℝ} (h : ∀ i, Differentiable ℝ (φ i))
    (j : Fin 3) : pdR j (fun y => ∑ i ∈ s, φ i y) = fun y => ∑ i ∈ s, pdR j (φ i) y := by
  funext y; simp only [pdR]
  rw [fderiv_fun_sum fun i _ => h i y]; simp

/-- Schwarz: partial derivatives commute on smooth fields. -/
lemma pdR_comm {φ : T3 → ℝ} (h : ContDiff ℝ ∞ φ) (a b : Fin 3) :
    pdR a (pdR b φ) = pdR b (pdR a φ) := by
  funext y
  have hs := ((h.of_le (WithTop.coe_le_coe.2 (le_top : (2:ℕ∞) ≤ ⊤)) : ContDiff ℝ 2 φ).contDiffAt (x := y)).isSymmSndFDerivAt (by simp)
  show fderiv ℝ (fun z => fderiv ℝ φ z (EuclideanSpace.single b 1)) y (EuclideanSpace.single a 1) =
    fderiv ℝ (fun z => fderiv ℝ φ z (EuclideanSpace.single a 1)) y (EuclideanSpace.single b 1)
  have hd : ∀ w, fderiv ℝ (fun z => fderiv ℝ φ z w) y = fun v => fderiv ℝ (fderiv ℝ φ) y v w :=
    fun w => by
      funext v
      rw [fderiv_clm_apply ((h.fderiv_right (m := ∞) le_rfl).differentiable (by simp) y)
        (differentiableAt_const _)]
      simp
  rw [hd, hd]; exact hs _ _

/-- Integration by parts on the unit cell. -/
lemma cellI_ibp {φ ψ : T3 → ℝ} (h : PerR φ) (h' : PerR ψ) (j : Fin 3) :
    cellI (fun y => pdR j φ y * ψ y) = -cellI (fun y => φ y * pdR j ψ y) := by
  have h0 := cellI_pdR (h.mul h') j
  rw [pdR_mul (h.1.differentiable (by simp)) (h'.1.differentiable (by simp))] at h0
  rw [cellI_add (φ := fun y => pdR j φ y * ψ y) (ψ := fun y => φ y * pdR j ψ y)
    ((h.pdR j).cont.mul h'.cont) (h.cont.mul (h'.pdR j).cont)] at h0
  linarith

/-- Pointwise two-term domination integrates. -/
lemma cellI_le_two {f p q : T3 → ℝ} (hf : Continuous f) (hp : Continuous p) (hq : Continuous q)
    (c₁ c₂ : ℝ) (hle : ∀ y, f y ≤ c₁ * p y + c₂ * q y) :
    cellI f ≤ c₁ * cellI p + c₂ * cellI q := by
  have := cellI_mono (ψ := fun y => c₁ * p y + c₂ * q y) hf (by fun_prop) hle
  rwa [cellI_add (φ := fun y => c₁ * p y) (ψ := fun y => c₂ * q y) (continuous_const.mul hp)
    (continuous_const.mul hq), cellI_const_mul, cellI_const_mul] at this

/-! ### Gagliardo–Nirenberg -/

/-- **Proved.** Gagliardo–Nirenberg on the unit cell: if `|g| ≤ M` then
`∫ (∂ₐg)⁴ ≤ 9 M² ∫ (∂ₐ∂ₐg)²`. -/
theorem gagliardoNirenberg_cell {g : T3 → ℝ} (hg : PerR g) {M : ℝ} (hM : ∀ y, |g y| ≤ M)
    (a : Fin 3) :
    cellI (fun y => pdR a g y ^ 4) ≤ 9 * M ^ 2 * cellI (fun y => pdR a (pdR a g) y ^ 2) := by
  set w := pdR a g with hw_def
  set z := pdR a w with hz_def
  have hw : PerR w := hg.pdR a
  have hz : PerR z := hw.pdR a
  set ψ : T3 → ℝ := fun y => w y * (w y * w y) with hψ_def
  have hψ : PerR ψ := hw.mul (hw.mul hw)
  have hdw : Differentiable ℝ w := hw.1.differentiable (by simp)
  have hdψ : pdR a ψ = fun y => z y * (w y * w y) + w y * (z y * w y + w y * z y) := by
    simp only [ψ]
    have hww : Differentiable ℝ (fun y => w y * w y) := hdw.mul hdw
    rw [pdR_mul hdw hww, pdR_mul hdw hdw]
  have hibp := cellI_ibp hg hψ a
  rw [hdψ] at hibp
  have hX : cellI (fun y => w y ^ 4) = cellI (fun y => -3 * (g y * (w y ^ 2 * z y))) := by
    have e1 : (fun y => w y ^ 4) = fun y => pdR a g y * ψ y := by
      funext y; simp only [ψ, ← hw_def]; ring
    have e2 : (fun y => -3 * (g y * (w y ^ 2 * z y))) =
        fun y => -(g y * (z y * (w y * w y) + w y * (z y * w y + w y * z y))) := by
      funext y; ring
    rw [e1, hibp, e2, cellI_neg]
  have hle : ∀ y, -3 * (g y * (w y ^ 2 * z y)) ≤ (1 / 2) * w y ^ 4 + (9 * M ^ 2 / 2) * z y ^ 2 :=
    fun y => by
      have h1 : -(g y * z y) ≤ M * |z y| := by
        calc -(g y * z y) ≤ |g y * z y| := neg_le_abs _
          _ = |g y| * |z y| := abs_mul _ _
          _ ≤ M * |z y| := mul_le_mul_of_nonneg_right (hM y) (abs_nonneg _)
      have h2 : 0 ≤ w y ^ 2 := sq_nonneg _
      have h3 : (M * |z y|) ^ 2 = M ^ 2 * z y ^ 2 := by rw [mul_pow, sq_abs]
      nlinarith [sq_nonneg (w y ^ 2 - 3 * (M * |z y|)), mul_le_mul_of_nonneg_left h1 h2]
  have hcont3 : Continuous fun y => -3 * (g y * (w y ^ 2 * z y)) :=
    continuous_const.mul (hg.cont.mul ((hw.cont.pow 2).mul hz.cont))
  have := cellI_le_two hcont3 (hw.cont.pow 4) (hz.cont.pow 2) _ _ hle
  rw [← hX] at this
  · linarith

end PeriodicNSContinuation
