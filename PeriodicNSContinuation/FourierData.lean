/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.LocalExistence

/-!
# Fourier data of smooth periodic initial data

**Proved:** `periodicDataDivFree`, `periodicDataHs s` (all real `s`), `galerkinContinuation ν s`,
and `periodicGalerkinUniformTime_of_gt'` (`0 ≤ ν`, `5/2 < s`, no named-Prop inputs).
**Not proved here:** `PeriodicGalerkinLimit`. Clay is not solved.
All declaration names in this file are coined (see README).
-/

noncomputable section
open Set MeasureTheory Complex FeffermanClayNS NavierStokes3D

namespace PeriodicNSContinuation

/-- Instance search does not find this in the pinned Mathlib; supplied from `NormedSpace`. -/
local instance : ContinuousSMul ℝ ℂ :=
  (NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := ℂ)).continuousSMul

/-- Unit-cube Fourier coefficient of a complex function on `ℝ³` (coined). -/
def cubeCoeff (g : (Fin 3 → ℝ) → ℂ) (k : Fin 3 → ℤ) : ℂ :=
  ∫ x in Icc (0 : Fin 3 → ℝ) 1,
    g x * Complex.exp (-(2 * Real.pi * Complex.I) * ∑ j, ((k j : ℝ) : ℂ) * (x j : ℂ))

/-- Partial derivative in coordinate direction `j` (coined). -/
def pdC (j : Fin 3) (g : (Fin 3 → ℝ) → ℂ) : (Fin 3 → ℝ) → ℂ :=
  fun x => fderiv ℝ g x (Pi.single j 1)

lemma insertNth_one_eq (j : Fin (2 + 1)) (y : Fin 2 → ℝ) :
    (Fin.insertNth j (1 : ℝ) y : Fin 3 → ℝ) = Fin.insertNth j (0 : ℝ) y + Pi.single j 1 := by
  ext m
  rcases Fin.eq_self_or_eq_succAbove j m with h | ⟨m', rfl⟩
  · subst h; simp
  · simp [Fin.succAbove_ne]

/-- **Proved.** The integral of `∂_j h` over the unit cube vanishes for `C¹` `h` that is
`1`-periodic in direction `j`. -/
theorem integral_pdC_eq_zero (j : Fin 3) (h : (Fin 3 → ℝ) → ℂ) (hh : ContDiff ℝ 1 h)
    (hper : ∀ x, h (x + Pi.single j 1) = h x) :
    ∫ x in Icc (0 : Fin 3 → ℝ) 1, pdC j h x = 0 := by
  have hd : ∀ x, HasFDerivAt h (fderiv ℝ h x) x := fun x =>
    (hh.differentiable one_ne_zero x).hasFDerivAt
  have hcont : Continuous fun x => pdC j h x :=
    (hh.continuous_fderiv one_ne_zero).clm_apply continuous_const
  set F' : Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] ℂ := Pi.single j (fun x => fderiv ℝ h x)
    with hF'
  have := integral_divergence_of_hasFDerivAt_off_countable' (n := 2) (a := 0) (b := 1)
    (zero_le_one) (Pi.single j h) F' ∅ countable_empty
    (fun i => by
      by_cases hij : i = j
      · subst hij; simpa using hh.continuous.continuousOn
      · simp [hij]; exact continuousOn_const)
    (fun x _ i => by
      by_cases hij : i = j
      · subst hij; simpa [hF'] using hd x
      · simp only [hF', Pi.single_apply, hij, if_false]; exact hasFDerivAt_const 0 x)
    (by
      refine (Continuous.integrableOn_Icc (continuous_finset_sum _ fun i _ => ?_))
      by_cases hij : i = j
      · subst hij; simpa [hF'] using (hh.continuous_fderiv one_ne_zero).clm_apply continuous_const
      · simp [hF', hij]; exact continuous_const)
  have hsum : ∀ x, (∑ i, F' i x (Pi.single i 1)) = pdC j h x :=
    fun x => by
      rw [Finset.sum_eq_single j (fun i _ hij => by simp [hF', hij]) (by simp)]
      simp [hF', pdC]
  simp only [hsum] at this
  rw [this]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hij : i = j
  · subst hij
    simp only [Pi.single_eq_same, Pi.one_apply, Pi.zero_apply]
    rw [sub_eq_zero]
    refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
    rw [insertNth_one_eq, hper]
  · simp [hij]

/-- The character `x ↦ exp(-2πi k·x)` (coined). -/
def charK (k : Fin 3 → ℤ) (x : Fin 3 → ℝ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) * ∑ j, ((k j : ℝ) : ℂ) * (x j : ℂ))

lemma cubeCoeff_eq (g : (Fin 3 → ℝ) → ℂ) (k : Fin 3 → ℤ) :
    cubeCoeff g k = ∫ x in Icc (0 : Fin 3 → ℝ) 1, g x * charK k x := rfl

/-- The linear phase `x ↦ -2πi k·x` (coined). -/
def phaseCLM (k : Fin 3 → ℤ) : (Fin 3 → ℝ) →L[ℝ] ℂ :=
  ∑ m, (-(2 * Real.pi * Complex.I) * ((k m : ℝ) : ℂ)) •
    (Complex.ofRealCLM.comp (ContinuousLinearMap.proj m))

lemma phaseCLM_apply (k : Fin 3 → ℤ) (x : Fin 3 → ℝ) :
    phaseCLM k x = -(2 * Real.pi * Complex.I) * ∑ j, ((k j : ℝ) : ℂ) * (x j : ℂ) := by
  simp only [phaseCLM, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

lemma charK_eq (k : Fin 3 → ℤ) : charK k = fun x => Complex.exp (phaseCLM k x) := by
  funext x; rw [phaseCLM_apply]; rfl

lemma charK_contDiff (k : Fin 3 → ℤ) {n : WithTop ℕ∞} : ContDiff ℝ n (charK k) := by
  rw [charK_eq]; exact Complex.contDiff_exp.comp (phaseCLM k).contDiff

lemma charK_hasFDerivAt (k : Fin 3 → ℤ) (x : Fin 3 → ℝ) :
    HasFDerivAt (charK k) (charK k x • phaseCLM k) x := by
  rw [charK_eq]
  have := (Complex.hasDerivAt_exp (phaseCLM k x)).comp_hasFDerivAt x (phaseCLM k).hasFDerivAt
  simpa [charK_eq] using this

lemma phaseCLM_single (k : Fin 3 → ℤ) (j : Fin 3) :
    phaseCLM k (Pi.single j 1) = -(2 * Real.pi * Complex.I) * ((k j : ℝ) : ℂ) := by
  rw [phaseCLM_apply]
  congr 1
  rw [Finset.sum_eq_single j (fun i _ hij => by simp [hij]) (by simp)]
  simp

lemma charK_add_single (k : Fin 3 → ℤ) (j : Fin 3) (x : Fin 3 → ℝ) :
    charK k (x + Pi.single j 1) = charK k x := by
  rw [charK_eq]
  simp only [map_add, phaseCLM_single, Complex.exp_add]
  have : Complex.exp (-(2 * Real.pi * Complex.I) * ((k j : ℝ) : ℂ)) = 1 := by
    rw [Complex.exp_eq_one_iff]
    exact ⟨-k j, by push_cast; ring⟩
  rw [this, mul_one]

lemma norm_charK (k : Fin 3 → ℤ) (x : Fin 3 → ℝ) : ‖charK k x‖ = 1 := by
  rw [charK, Complex.norm_exp]
  have : (-(2 * Real.pi * Complex.I) * ∑ j, ((k j : ℝ) : ℂ) * (x j : ℂ)).re = 0 := by
    have h : (∑ j, ((k j : ℝ) : ℂ) * (x j : ℂ)) = ((∑ j, (k j : ℝ) * x j : ℝ) : ℂ) := by
      push_cast; rfl
    rw [h]; simp
  rw [this, Real.exp_zero]

/-- **Proved.** Fourier coefficient of a derivative: `(∂_j g)^(k) = 2πi k_j ĝ(k)` for `C¹` `g`
that is `1`-periodic in direction `j`. -/
theorem cubeCoeff_pdC (j : Fin 3) (g : (Fin 3 → ℝ) → ℂ) (hg : ContDiff ℝ 1 g)
    (hper : ∀ x, g (x + Pi.single j 1) = g x) (k : Fin 3 → ℤ) :
    cubeCoeff (pdC j g) k = 2 * Real.pi * Complex.I * ((k j : ℝ) : ℂ) * cubeCoeff g k := by
  set c : ℂ := -(2 * Real.pi * Complex.I) * ((k j : ℝ) : ℂ) with hc
  have hh : ContDiff ℝ 1 (fun x => g x * charK k x) := hg.mul (charK_contDiff k)
  have h0 := integral_pdC_eq_zero j (fun x => g x * charK k x) hh
    (fun x => by simp only [hper, charK_add_single])
  have hpd : ∀ x, pdC j (fun x => g x * charK k x) x =
      g x * charK k x * c + pdC j g x * charK k x := fun x => by
    have := ((hg.differentiable one_ne_zero x).hasFDerivAt).mul (charK_hasFDerivAt k x)
    simp only [pdC]
    have e := congrArg (fun L => L (Pi.single j (1:ℝ))) this.fderiv
    simp only at e
    refine (show _ = _ from e).trans ?_
    show g x * (charK k x * phaseCLM k (Pi.single j 1)) +
      charK k x * fderiv ℝ g x (Pi.single j 1) = _
    rw [phaseCLM_single, hc]
    ring
  simp only [hpd] at h0
  have hc1 : Continuous fun x => g x * charK k x * c :=
    (hg.continuous.mul (charK_contDiff k (n := 0)).continuous).mul continuous_const
  have hc2 : Continuous fun x => pdC j g x * charK k x :=
    ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
      (charK_contDiff k (n := 0)).continuous
  rw [integral_add (hc1.integrableOn_Icc) (hc2.integrableOn_Icc)] at h0
  rw [cubeCoeff_eq, cubeCoeff_eq]
  have hm : ∫ a in Icc (0 : Fin 3 → ℝ) 1, g a * charK k a * c =
      (∫ a in Icc (0 : Fin 3 → ℝ) 1, g a * charK k a) * c :=
    integral_mul_const c _
  rw [hc] at hm
  linear_combination h0 - hm
  
/-- Component `i` of a velocity field, read in cube coordinates, as a complex function (coined). -/
def compC (u₀ : NavierStokes3D.VelocityField) (i : Fin 3) : (Fin 3 → ℝ) → ℂ :=
  fun x => ((u₀ ((EuclideanSpace.equiv (Fin 3) ℝ).symm x) i : ℝ) : ℂ)

lemma fourierCoeffVF_eq_cubeCoeff (u₀ : NavierStokes3D.VelocityField) (k : Fin 3 → ℤ) (i : Fin 3) :
    fourierCoeffVF u₀ k i = cubeCoeff (compC u₀ i) k := rfl

lemma equiv_symm_single (j : Fin 3) :
    (EuclideanSpace.equiv (Fin 3) ℝ).symm (Pi.single j 1) = EuclideanSpace.single j (1 : ℝ) := by
  ext m; simp

lemma compC_contDiff {u₀ : NavierStokes3D.VelocityField} (hu : ContDiff ℝ (⊤ : ℕ∞) u₀)
    (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (compC u₀ i) := by
  have := Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj i : T3 →L[ℝ] ℝ).contDiff.comp
    (hu.comp (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff))
  exact this

lemma compC_add_single {u₀ : NavierStokes3D.VelocityField} (hp : IsZ3Periodic u₀) (i j : Fin 3)
    (x : Fin 3 → ℝ) : compC u₀ i (x + Pi.single j 1) = compC u₀ i x := by
  simp only [compC, map_add, equiv_symm_single]
  rw [show (EuclideanSpace.single j (1 : ℝ) : T3) = stdBasisVec j from rfl,
    (isZ3Periodic_iff_unit_shifts u₀).1 hp]

lemma pdC_compC {u₀ : NavierStokes3D.VelocityField} (hu : ContDiff ℝ (⊤ : ℕ∞) u₀) (i : Fin 3)
    (x : Fin 3 → ℝ) :
    pdC i (compC u₀ i) x = ((fderiv ℝ (fun y => u₀ y i) ((EuclideanSpace.equiv (Fin 3) ℝ).symm x)
      (EuclideanSpace.single i 1) : ℝ) : ℂ) := by
  have hφ : Differentiable ℝ (fun y : T3 => u₀ y i) := by
    have := ((EuclideanSpace.proj i : T3 →L[ℝ] ℝ).contDiff.comp hu).differentiable (by simp)
    exact this
  have h := Complex.ofRealCLM.hasFDerivAt.comp x
    ((hφ _).hasFDerivAt.comp x (EuclideanSpace.equiv (Fin 3) ℝ).symm.hasFDerivAt)
  simp only [pdC]
  rw [show compC u₀ i = Complex.ofRealCLM ∘ (fun y : T3 => u₀ y i) ∘
    (EuclideanSpace.equiv (Fin 3) ℝ).symm from rfl, h.fderiv]
  simp

/-- **Proved.** Smooth divergence-free periodic data have divergence-free Fourier coefficients.
This discharges the named Prop `PeriodicDataDivFree`. -/
theorem periodicDataDivFree : PeriodicDataDivFree := by
  intro u₀ ⟨hu, hdiv, hp⟩ k
  have hsum : ∑ i, cubeCoeff (pdC i (compC u₀ i)) k = 0 := by
    have hint : ∀ i ∈ Finset.univ, IntegrableOn
        (fun x => pdC i (compC u₀ i) x * charK k x) (Icc (0 : Fin 3 → ℝ) 1) := fun i _ =>
      (((compC_contDiff hu i).continuous_fderiv (by simp)).clm_apply continuous_const |>.mul
        (charK_contDiff k (n := 0)).continuous).integrableOn_Icc
    simp only [cubeCoeff_eq]
    rw [← integral_finset_sum _ hint]
    refine (setIntegral_congr_fun measurableSet_Icc fun x _ => ?_).trans (integral_zero _ _)
    rw [← Finset.sum_mul]
    simp only [pdC_compC hu]
    rw [← Complex.ofReal_sum]
    have := hdiv ((EuclideanSpace.equiv (Fin 3) ℝ).symm x)
    simp only [NavierStokes3D.div] at this
    rw [this]; simp
  simp only [fun i => cubeCoeff_pdC i (compC u₀ i)
    ((compC_contDiff hu i).of_le (by simp)) (compC_add_single hp i i) k] at hsum
  simp only [TorusFourierNS.dot, TorusFourierNS.kvec, fourierCoeffVF_eq_cubeCoeff]
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have : (2 * Real.pi * Complex.I : ℂ) * ∑ i, ((k i : ℝ) : ℂ) * cubeCoeff (compC u₀ i) k = 0 := by
    rw [Finset.mul_sum]; rw [← hsum]
    refine Finset.sum_congr rfl fun i _ => by ring
  exact (mul_eq_zero.1 this).resolve_left h2

/-- Smooth and `1`-periodic in every coordinate direction (coined). -/
def SmoothPer (g : (Fin 3 → ℝ) → ℂ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) g ∧ ∀ (j : Fin 3) x, g (x + Pi.single j 1) = g x

lemma SmoothPer.pdC {g : (Fin 3 → ℝ) → ℂ} (hg : SmoothPer g) (j : Fin 3) :
    SmoothPer (pdC j g) := by
  refine ⟨?_, fun m x => ?_⟩
  · have := (hg.1.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by
      rw [← WithTop.coe_one, ← WithTop.coe_add]; exact WithTop.coe_le_coe.2 le_top)).clm_apply
      (contDiff_const (c := (Pi.single j 1 : Fin 3 → ℝ)))
    exact this
  · simp only [PeriodicNSContinuation.pdC]
    rw [← fderiv_comp_add_right]
    congr 2
    funext y; exact hg.2 m y

lemma SmoothPer.continuous {g : (Fin 3 → ℝ) → ℂ} (hg : SmoothPer g) : Continuous g :=
  hg.1.continuous

/-- `g - (4π²)⁻¹ Σ_j ∂_j² g`, i.e. `1 - Δ/(4π²)` (coined). -/
def helmOp (g : (Fin 3 → ℝ) → ℂ) : (Fin 3 → ℝ) → ℂ :=
  fun x => g x - ((4 * Real.pi ^ 2 : ℝ) : ℂ)⁻¹ * ∑ j, pdC j (pdC j g) x

lemma SmoothPer.helmOp {g : (Fin 3 → ℝ) → ℂ} (hg : SmoothPer g) : SmoothPer (helmOp g) := by
  refine ⟨hg.1.sub (contDiff_const.mul (ContDiff.sum fun j _ => ((hg.pdC j).pdC j).1)),
    fun m x => ?_⟩
  simp only [PeriodicNSContinuation.helmOp, hg.2 m x, fun j => ((hg.pdC j).pdC j).2 m x]

lemma integrableOn_coeff {g : (Fin 3 → ℝ) → ℂ} (hg : Continuous g) (k : Fin 3 → ℤ) :
    IntegrableOn (fun x => g x * charK k x) (Icc (0 : Fin 3 → ℝ) 1) :=
  (hg.mul (charK_contDiff k (n := 0)).continuous).integrableOn_Icc

/-- **Proved.** `(1 - Δ/(4π²))` acts on cube coefficients by `1 + |k|²`. -/
theorem cubeCoeff_helmOp {g : (Fin 3 → ℝ) → ℂ} (hg : SmoothPer g) (k : Fin 3 → ℤ) :
    cubeCoeff (helmOp g) k = ((1 + ∑ j, ((k j : ℝ)) ^ 2 : ℝ) : ℂ) * cubeCoeff g k := by
  have hc : ∀ j, Continuous (pdC j (pdC j g)) := fun j => ((hg.pdC j).pdC j).continuous
  have h2 : ∀ j, cubeCoeff (pdC j (pdC j g)) k =
      (2 * Real.pi * Complex.I * ((k j : ℝ) : ℂ)) ^ 2 * cubeCoeff g k := fun j => by
    rw [cubeCoeff_pdC j _ ((hg.pdC j).1.of_le (by simp)) ((hg.pdC j).2 j),
      cubeCoeff_pdC j _ (hg.1.of_le (by simp)) (hg.2 j)]
    ring
  have hlin : cubeCoeff (helmOp g) k = cubeCoeff g k -
      ((4 * Real.pi ^ 2 : ℝ) : ℂ)⁻¹ * ∑ j, cubeCoeff (pdC j (pdC j g)) k := by
    simp only [cubeCoeff_eq, PeriodicNSContinuation.helmOp, sub_mul, mul_assoc, Finset.sum_mul]
    have hcm := integral_const_mul (μ := volume.restrict (Icc (0 : Fin 3 → ℝ) 1))
      (((4 * Real.pi ^ 2 : ℝ) : ℂ)⁻¹) (fun a => ∑ i, pdC i (pdC i g) a * charK k a)
    rw [integral_sub (integrableOn_coeff hg.continuous k)]
    · congr 1
      refine (show _ = _ from hcm).trans ?_
      congr 1
      exact integral_finset_sum _ fun j _ => integrableOn_coeff (hc j) k
    exact (Integrable.const_mul (integrable_finset_sum _ fun j _ =>
      integrableOn_coeff (hc j) k) _)
  rw [hlin]
  simp only [h2]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  rw [← Finset.sum_mul]
  field_simp
  simp only [Complex.I_sq]
  ring_nf
  simp only [Finset.sum_neg_distrib, Finset.sum_mul, Finset.mul_sum]
  ring_nf
  rw [Finset.mul_sum]; ring_nf

lemma smoothPer_iterate_helmOp {g : (Fin 3 → ℝ) → ℂ} (hg : SmoothPer g) (m : ℕ) :
    SmoothPer ((PeriodicNSContinuation.helmOp)^[m] g) := by
  induction m with
  | zero => exact hg
  | succ m ih => rw [Function.iterate_succ_apply']; exact ih.helmOp

theorem cubeCoeff_iterate_helmOp {g : (Fin 3 → ℝ) → ℂ} (hg : SmoothPer g) (m : ℕ)
    (k : Fin 3 → ℤ) : cubeCoeff ((PeriodicNSContinuation.helmOp)^[m] g) k =
      ((1 + ∑ j, ((k j : ℝ)) ^ 2 : ℝ) : ℂ) ^ m * cubeCoeff g k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', cubeCoeff_helmOp (smoothPer_iterate_helmOp hg m), ih]; ring

/-- **Proved.** Cube coefficients of a continuous function are uniformly bounded. -/
theorem exists_bound_cubeCoeff {g : (Fin 3 → ℝ) → ℂ} (hg : Continuous g) :
    ∃ B, 0 ≤ B ∧ ∀ k, ‖cubeCoeff g k‖ ≤ B := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : Fin 3 → ℝ)) (b := 1)).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun k => ?_⟩
  have hvol : (volume (Icc (0 : Fin 3 → ℝ) 1)) = 1 := by simp [Real.volume_Icc_pi]
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (0 : Fin 3 → ℝ) 1)
    (f := fun x => g x * charK k x) (C := max C 0) (by rw [hvol]; simp) (fun x hx => by
      rw [norm_mul, norm_charK, mul_one]; exact (hC x hx).trans (le_max_left _ _))
  rw [Measure.real, hvol] at h
  simpa [cubeCoeff_eq] using h

/-- **Proved.** Smooth periodic functions have rapidly decaying cube coefficients:
`Σ_k (1+|k|²)^s |ĝ(k)|² < ∞` for every real `s`. -/
theorem summable_sobW_cubeCoeff {g : (Fin 3 → ℝ) → ℂ} (hg : SmoothPer g) (s : ℝ) :
    Summable fun k : Fin 3 → ℤ => TorusFourierNS.sobW s k * ‖cubeCoeff g k‖ ^ 2 := by
  set m : ℕ := ⌈s⌉₊ + 2
  obtain ⟨B, hB0, hB⟩ := exists_bound_cubeCoeff (smoothPer_iterate_helmOp hg m).continuous
  have hms : 3 / 2 < 2 * (m : ℝ) - s := by
    have h1 := Nat.le_ceil s
    have h2 : (0 : ℝ) ≤ ⌈s⌉₊ := Nat.cast_nonneg _
    simp only [m]; push_cast; linarith
  have hsum := (TorusFourierNS.summable_sobW_neg hms).mul_right (B ^ 2)
  rw [neg_sub] at hsum
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (Real.rpow_nonneg
    (TorusFourierNS.one_add_sq_pos k).le _) (sq_nonneg _)) (fun k => ?_) hsum
  set w : ℝ := 1 + ∑ j, ((k j : ℝ)) ^ 2
  have hw : 0 < w := TorusFourierNS.one_add_sq_pos k
  have hk := hB k
  rw [cubeCoeff_iterate_helmOp hg, norm_mul, norm_pow, Complex.norm_of_nonneg hw.le] at hk
  have e : TorusFourierNS.sobW s k = TorusFourierNS.sobW (s - 2 * m) k * (w ^ m) ^ 2 := by
    unfold TorusFourierNS.sobW
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_add hw]
    congr 1; push_cast; ring
  calc TorusFourierNS.sobW s k * ‖cubeCoeff g k‖ ^ 2
      = TorusFourierNS.sobW (s - 2 * m) k * (w ^ m * ‖cubeCoeff g k‖) ^ 2 := by rw [e]; ring
    _ ≤ TorusFourierNS.sobW (s - 2 * m) k * B ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hk 2)
          (Real.rpow_nonneg hw.le _)

/-- **Proved.** `PeriodicDataHs s` holds for every real `s`. -/
theorem periodicDataHs (s : ℝ) : PeriodicDataHs s := by
  intro u₀ ⟨hu, _, hp⟩
  have hS : ∀ i, SmoothPer (compC u₀ i) := fun i => ⟨compC_contDiff hu i, fun j x =>
    compC_add_single hp i j x⟩
  unfold TorusFourierNS.MemHsField
  refine (summable_prod_of_nonneg fun p => mul_nonneg (Real.rpow_nonneg
    (TorusFourierNS.one_add_sq_pos p.1).le _) (sq_nonneg _)).2 ⟨fun _ => Summable.of_finite, ?_⟩
  simp only [tsum_fintype, fourierCoeffVF_eq_cubeCoeff]
  exact summable_sum fun i _ => summable_sobW_cubeCoeff (hS i) s

/-- **Proved.** `GalerkinContinuation ν s` holds for all `ν s`
(from `TorusFourierNS.galerkinNS_continuation_of_hsBound`). -/
theorem galerkinContinuation (ν s : ℝ) : GalerkinContinuation ν s := by
  intro N a T M hT hB
  obtain ⟨α, h0, hd⟩ := TorusFourierNS.galerkinNS_continuation_of_hsBound ν s
    (TorusFourierNS.restrictG N a) hT M fun T' hT' α h0 hd => hB T' hT' α ⟨h0, hd⟩
  exact ⟨α, h0, hd⟩

/-- **Proved.** Uniform Galerkin existence time for `ν ≥ 0`, `s > 5/2`, with no remaining
named-Prop inputs. -/
theorem periodicGalerkinUniformTime_of_gt' {ν s : ℝ} (hν : 0 ≤ ν) (hs : 5 / 2 < s) :
    PeriodicGalerkinUniformTime ν s :=
  periodicGalerkinUniformTime_of_gt hν hs (periodicDataHs s) periodicDataDivFree
    (galerkinContinuation ν s)

end PeriodicNSContinuation
