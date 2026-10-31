/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.HsEnergyIdentity
import PeriodicNSContinuation.Energy

/-!
# The Fourier-coefficient ODE of a classical periodic solution (names coined)
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D TorusFourierNS
open scoped ContDiff

namespace PeriodicNSContinuation

local instance : ContinuousSMul ℝ ℂ :=
  (NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := ℂ)).continuousSMul

local notation "Eq3" => EuclideanSpace.equiv (Fin 3) ℝ

/-- Complexified lift of a real scalar field on `T3` to `Fin 3 → ℝ` (coined). -/
def liftR (φ : T3 → ℝ) : (Fin 3 → ℝ) → ℂ := fun x => ((φ ((Eq3).symm x) : ℝ) : ℂ)

/-- Directional derivative along the `j`-th unit vector (coined). -/
def pdR (j : Fin 3) (φ : T3 → ℝ) : T3 → ℝ := fun y => fderiv ℝ φ y (EuclideanSpace.single j 1)

/-- Smooth and `1`-periodic in each coordinate direction (coined). -/
def PerR (φ : T3 → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ ∀ x j, φ (x + EuclideanSpace.single j 1) = φ x

lemma PerR.pdR {φ : T3 → ℝ} (h : PerR φ) (j : Fin 3) : PerR (pdR j φ) := by
  refine ⟨(h.1.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const, fun x i => ?_⟩
  simp only [PeriodicNSContinuation.pdR]
  rw [← fderiv_comp_add_right]
  congr 2; funext y; exact h.2 y i

lemma liftR_contDiff {φ : T3 → ℝ} (h : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (liftR φ) :=
  Complex.ofRealCLM.contDiff.comp (h.comp (Eq3).symm.contDiff)

lemma liftR_add_single {φ : T3 → ℝ} (h : PerR φ) (j : Fin 3) (x : Fin 3 → ℝ) :
    liftR φ (x + Pi.single j 1) = liftR φ x := by
  simp only [liftR, map_add, equiv_symm_single, h.2]

lemma pdC_liftR {φ : T3 → ℝ} (hφ : Differentiable ℝ φ) (j : Fin 3) (x : Fin 3 → ℝ) :
    pdC j (liftR φ) x = liftR (pdR j φ) x := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp x
    ((hφ _).hasFDerivAt.comp x (Eq3).symm.hasFDerivAt)
  simp only [pdC]
  rw [show liftR φ = Complex.ofRealCLM ∘ φ ∘ (Eq3).symm from rfl, h.fderiv]
  simp [liftR, PeriodicNSContinuation.pdR]

/-- **Proved.** `(∂_j φ)^(k) = 2πi k_j φ̂(k)`. -/
lemma cubeCoeff_pdR {φ : T3 → ℝ} (h : PerR φ) (j : Fin 3) (k : Fin 3 → ℤ) :
    cubeCoeff (liftR (pdR j φ)) k = 2 * Real.pi * Complex.I * ((k j : ℝ) : ℂ) *
      cubeCoeff (liftR φ) k := by
  have e : liftR (pdR j φ) = pdC j (liftR φ) :=
    funext fun x => (pdC_liftR (h.1.differentiable (by simp)) j x).symm
  rw [e, cubeCoeff_pdC j _ ((liftR_contDiff h.1).of_le (by simp)) (liftR_add_single h j) k]

lemma compC_eq_liftR (u : VelocityField) (i : Fin 3) : compC u i = liftR (fun y => u y i) := rfl

lemma fderiv_coord {f : T3 → T3} {y : T3} (hf : DifferentiableAt ℝ f y) (i : Fin 3) (w : T3) :
    fderiv ℝ (fun z => f z i) y w = fderiv ℝ f y w i := by
  have h := (EuclideanSpace.proj i : T3 →L[ℝ] ℝ).hasFDerivAt.comp y hf.hasFDerivAt
  rw [show (fun z => f z i) = (EuclideanSpace.proj i : T3 →L[ℝ] ℝ) ∘ f from rfl, h.fderiv]
  simp

lemma laplacian_coord {f : T3 → T3} (hf : ContDiff ℝ ∞ f) (x : T3) (i : Fin 3) :
    laplacian f x i = ∑ j, pdR j (pdR j (fun y => f y i)) x := by
  simp only [laplacian]
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hG : Differentiable ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) :=
    ((hf.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const).differentiable (by simp)
  have e : pdR j (fun y => f y i) = fun y => fderiv ℝ f y (EuclideanSpace.single j 1) i := by
    funext y; exact fderiv_coord ((hf.differentiable (by simp)) y) i _
  simp only [PeriodicNSContinuation.pdR] at e ⊢
  rw [e, fderiv_coord (hG x)]

lemma convective_coord {u v : T3 → T3} (hv : Differentiable ℝ v) (x : T3) (i : Fin 3) :
    convective u v x i = ∑ l, u x l * pdR l (fun y => v y i) x := by
  simp only [convective, PeriodicNSContinuation.pdR, fderiv_coord (hv x)]
  conv_lhs => rw [show u x = ∑ l, u x l • EuclideanSpace.single l (1 : ℝ) by
    ext m; simp [Finset.sum_apply, Pi.single_apply]]
  simp [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply]

lemma pressureGradient_coord {p : T3 → ℝ} (hp : Differentiable ℝ p) (x : T3) (i : Fin 3) :
    pressureGradient p x i = pdR i p x :=
  gradient_coord p x i (hp x)

lemma phase_mul_charK (m k : Mode) (x : Fin 3 → ℝ) :
    phase m ((Eq3).symm x) * charK k x = charK (k - m) x := by
  simp only [phase, charK, ← Complex.exp_add]
  congr 1
  simp only [Pi.sub_apply, Int.cast_sub, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib]
  simp
  ring

/-- **Proved.** Fourier coefficient of a product with an absolutely convergent Fourier series:
`(g f)^(k) = ∑ₘ bₘ f̂(k-m)`. -/
lemma cubeCoeff_mul_series {f g : (Fin 3 → ℝ) → ℂ} (hf : Continuous f) {b : Mode → ℂ}
    (hb : Summable fun m => ‖b m‖)
    (hg : ∀ x, HasSum (fun m => b m * phase m ((Eq3).symm x)) (g x)) (k : Mode) :
    cubeCoeff (fun x => g x * f x) k = ∑' m, b m * cubeCoeff f (k - m) := by
  set F : Mode → (Fin 3 → ℝ) → ℂ := fun m x => b m * (f x * charK (k - m) x) with hF
  have hint : ∀ m, Integrable (F m) (volume.restrict (Icc (0 : Fin 3 → ℝ) 1)) := fun m =>
    (continuous_const.mul (hf.mul (charK_contDiff (n := 0) (k - m)).continuous)).integrableOn_Icc
  have hnorm : ∀ m, ∫ x in Icc (0 : Fin 3 → ℝ) 1, ‖F m x‖ =
      ‖b m‖ * ∫ x in Icc (0 : Fin 3 → ℝ) 1, ‖f x‖ := by
    intro m; rw [← integral_const_mul]; congr 1; funext x
    simp [hF, norm_charK]
  have hsum : Summable fun m => ∫ x in Icc (0 : Fin 3 → ℝ) 1, ‖F m x‖ := by
    simp_rw [hnorm]; exact hb.mul_right _
  have key := integral_tsum_of_summable_integral_norm hint hsum
  rw [cubeCoeff_eq]
  have e : ∀ x, g x * f x * charK k x = ∑' m, F m x := by
    intro x
    rw [mul_assoc, ← ((hg x).mul_right (f x * charK k x)).tsum_eq]
    congr 1; funext m; simp only [hF, ← phase_mul_charK m k x]; ring
  simp_rw [e, ← key]
  congr 1; funext m
  simp only [hF, cubeCoeff_eq]
  exact integral_const_mul _ _

/-- **Proved.** Differentiation under the integral: at an interior time, the `k`-th coefficient of
a jointly smooth field is differentiable with derivative the coefficient of `∂ₜu`. -/
lemma hasDerivAt_coeff_time {T : ℝ} {u : TimeDependentVelocity}
    (hu : ContDiffOn ℝ ∞ (fun q : ℝ × T3 => u q.1 q.2) (Corrected.S T)) {t : ℝ}
    (ht : t ∈ Ioo 0 T) (k : Mode) (i : Fin 3) :
    HasDerivAt (fun τ => fourierCoeffVF (u τ) k i)
      (cubeCoeff (liftR (fun y => Corrected.D T u (t, y) (1, 0) i)) k) t := by
  have hT : 0 < T := ht.1.trans ht.2
  set δ := min t (T - t) / 2 with hδ
  have hδ0 : 0 < δ := by have := lt_min ht.1 (sub_pos.2 ht.2); linarith
  have hδt : δ < t := by have := min_le_left t (T - t); linarith [ht.1]
  have hδT : t + δ < T := by have := min_le_right t (T - t); linarith [ht.2]
  set s := Icc (t - δ) (t + δ)
  have hsI : s ⊆ Ioo 0 T := fun τ hτ => ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hsn : s ∈ 𝓝 t := Icc_mem_nhds (by linarith) (by linarith)
  have hcont : ∀ τ ∈ Icc (0 : ℝ) T, Continuous (compC (u τ) i) := fun τ hτ =>
    (compC_contDiff (Corrected.contDiff_slice hu hτ) i).continuous
  set G : ℝ × T3 → ℝ := fun q => Corrected.D T u q (1, 0) i
  have hG : ContinuousOn G (Corrected.S T) := by
    have := (Corrected.continuousOn_D hu hT).clm_apply
      (continuousOn_const (c := ((1 : ℝ), (0 : T3))))
    exact (PiLp.continuous_apply 2 _ i).comp_continuousOn this
  have hG' : Continuous (liftR (fun y => G (t, y))) := by
    refine Complex.continuous_ofReal.comp (hG.comp_continuous ?_ fun _ => ⟨Ioo_subset_Icc_self ht,
      trivial⟩)
    exact continuous_const.prodMk (Eq3).symm.continuous
  set K : Set (ℝ × T3) := s ×ˢ ((Eq3).symm '' Icc (0 : Fin 3 → ℝ) 1)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.image (Eq3).symm.continuous)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (hG.mono fun q hq => ⟨Ioo_subset_Icc_self (hsI hq.1), trivial⟩)
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Icc (0 : Fin 3 → ℝ) 1))
    (F := fun τ x => compC (u τ) i x * charK k x)
    (F' := fun τ x => liftR (fun y => G (τ, y)) x * charK k x) (bound := fun _ => C) hsn
    ?_ ?_ ?_ ?_ (continuous_const.integrableOn_Icc) ?_
  · exact this.2
  · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with τ hτ
    exact ((hcont τ (Ioo_subset_Icc_self hτ)).mul
      (charK_contDiff (n := 0) k).continuous).aestronglyMeasurable
  · exact ((hcont t (Ioo_subset_Icc_self ht)).mul
      (charK_contDiff (n := 0) k).continuous).integrableOn_Icc
  · exact (hG'.mul (charK_contDiff (n := 0) k).continuous).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Icc fun x hx τ hτ => ?_
    rw [norm_mul, norm_charK, mul_one]
    simpa [liftR, G] using hC (τ, (Eq3).symm x) ⟨hτ, x, hx, rfl⟩
  · refine Eventually.of_forall fun x τ hτ => ?_
    have hτ' := Ioo_subset_Icc_self (hsI hτ)
    have h1 := (Corrected.hasDerivWithinAt_time hu hτ' ((Eq3).symm x)).hasDerivAt
      (Icc_mem_nhds (hsI hτ).1 (hsI hτ).2)
    have h2 := ((EuclideanSpace.proj i : T3 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt τ h1).ofReal_comp
    exact h2.mul_const (charK k x)

lemma integrableOn_cube_of_continuous {f : (Fin 3 → ℝ) → ℂ} (hf : Continuous f) (k : Mode) :
    Integrable (fun x => f x * charK k x) (volume.restrict (Icc (0 : Fin 3 → ℝ) 1)) :=
  (hf.mul (charK_contDiff (n := 0) k).continuous).integrableOn_Icc

lemma cubeCoeff_sub' {f g : (Fin 3 → ℝ) → ℂ} (hf : Continuous f) (hg : Continuous g) (k : Mode) :
    cubeCoeff (fun x => f x - g x) k = cubeCoeff f k - cubeCoeff g k := by
  simp only [cubeCoeff_eq, sub_mul]
  exact integral_sub (integrableOn_cube_of_continuous hf k) (integrableOn_cube_of_continuous hg k)

lemma cubeCoeff_const_mul' (c : ℂ) (f : (Fin 3 → ℝ) → ℂ) (k : Mode) :
    cubeCoeff (fun x => c * f x) k = c * cubeCoeff f k := by
  simp only [cubeCoeff_eq, mul_assoc]; exact integral_const_mul _ _

lemma cubeCoeff_sum' {f : Fin 3 → (Fin 3 → ℝ) → ℂ} (hf : ∀ j, Continuous (f j)) (k : Mode) :
    cubeCoeff (fun x => ∑ j, f j x) k = ∑ j, cubeCoeff (f j) k := by
  simp only [cubeCoeff_eq, Finset.sum_mul]
  exact integral_finset_sum _ fun j _ => integrableOn_cube_of_continuous (hf j) k

lemma perR_coord {v : T3 → T3} (hv : ContDiff ℝ ∞ v) (hp : IsZ3Periodic v) (i : Fin 3) :
    PerR (fun y => v y i) :=
  ⟨(EuclideanSpace.proj i : T3 →L[ℝ] ℝ).contDiff.comp hv, fun x j => by
    simp only [show (EuclideanSpace.single j (1 : ℝ) : T3) = stdBasisVec j from rfl,
      (isZ3Periodic_iff_unit_shifts v).1 hp]⟩

lemma perR_of {φ : T3 → ℝ} (hv : ContDiff ℝ ∞ φ) (hp : IsZ3Periodic φ) : PerR φ :=
  ⟨hv, fun x j => by
    simp only [show (EuclideanSpace.single j (1 : ℝ) : T3) = stdBasisVec j from rfl,
      (isZ3Periodic_iff_unit_shifts φ).1 hp]⟩

lemma PerR.continuous_liftR {φ : T3 → ℝ} (h : PerR φ) : Continuous (liftR φ) :=
  (liftR_contDiff h.1).continuous

/-- **Proved.** Coefficients of `∂ₜu` at an interior time, read off from the NS equation
(`f = 0`): viscous, pressure and convective parts. -/
lemma cubeCoeff_dt_eq {ν : ℝ} {u₀ : VelocityField} {T : ℝ} {u : TimeDependentVelocity}
    {p : TimeDependentPressure} (hs : IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p)
    {t : ℝ} (ht : t ∈ Icc 0 T) (k : Mode) (i : Fin 3) :
    cubeCoeff (liftR (fun y => Corrected.D T u (t, y) (1, 0) i)) k =
      (ν : ℂ) * ∑ j, (2 * Real.pi * Complex.I * ((k j : ℝ) : ℂ)) ^ 2 *
          fourierCoeffVF (u t) k i
        - 2 * Real.pi * Complex.I * ((k i : ℝ) : ℂ) * cubeCoeff (liftR (p t)) k
        - ∑ l, cubeCoeff (fun x => liftR (fun y => u t y l) x *
            liftR (pdR l (fun y => u t y i)) x) k := by
  obtain ⟨hT, hpu, hpp, hu, hp, heq, -, -⟩ := hs
  have hut := Corrected.contDiff_slice hu ht
  have hpt : ContDiff ℝ ∞ (p t) := Corrected.contDiff_slice_p hp ht
  have hφ : ∀ l, PerR (fun y => u t y l) := fun l => perR_coord hut (hpu t ht) l
  have hP : PerR (p t) := perR_of hpt (hpp t ht)
  have hpt_eq : ∀ y, Corrected.D T u (t, y) (1, 0) i =
      ν * ∑ j, pdR j (pdR j (fun y => u t y i)) y - pdR i (p t) y
        - ∑ l, u t y l * pdR l (fun y => u t y i) y := by
    intro y
    have h := congrArg (fun v : T3 => v i) (heq t ht y)
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at h
    rw [Corrected.derivWithin_time hu hT ht, laplacian_coord hut,
      pressureGradient_coord (hpt.differentiable (by simp)),
      convective_coord (hut.differentiable (by simp))] at h
    have h0 : ((fun _ _ => (0 : T3)) : ℝ → T3 → T3) t y i = 0 := rfl
    rw [h0] at h; linarith
  have e : liftR (fun y => Corrected.D T u (t, y) (1, 0) i) = fun x =>
      ((ν : ℂ) * ∑ j, liftR (pdR j (pdR j (fun y => u t y i))) x - liftR (pdR i (p t)) x)
        - ∑ l, liftR (fun y => u t y l) x * liftR (pdR l (fun y => u t y i)) x := by
    funext x; simp only [liftR, hpt_eq]; push_cast; rfl
  have c2 : ∀ j, Continuous (liftR (pdR j (pdR j (fun y => u t y i)))) := fun j =>
    (((hφ i).pdR j).pdR j).continuous_liftR
  have cS : Continuous fun x => ∑ l, liftR (fun y => u t y l) x * liftR (pdR l (fun y => u t y i)) x :=
    continuous_finset_sum _ fun l _ => (hφ l).continuous_liftR.mul ((hφ i).pdR l).continuous_liftR
  have cV : Continuous fun x => (ν : ℂ) * ∑ j, liftR (pdR j (pdR j (fun y => u t y i))) x :=
    continuous_const.mul (continuous_finset_sum _ fun j _ => c2 j)
  rw [e, cubeCoeff_sub' (cV.sub (hP.pdR i).continuous_liftR) cS,
    cubeCoeff_sub' cV (hP.pdR i).continuous_liftR, cubeCoeff_const_mul' (ν : ℂ)
      (fun x => ∑ j, liftR (pdR j (pdR j (fun y => u t y i))) x), cubeCoeff_sum' c2,
    cubeCoeff_sum' (f := fun l x => liftR (fun y => u t y l) x * liftR (pdR l (fun y => u t y i)) x)
      fun l => (hφ l).continuous_liftR.mul ((hφ i).pdR l).continuous_liftR,
    cubeCoeff_pdR hP]
  congr 3
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cubeCoeff_pdR ((hφ i).pdR j), cubeCoeff_pdR (hφ i), fourierCoeffVF_eq_cubeCoeff,
    compC_eq_liftR]; ring

lemma norm_cubeCoeff_le {f : (Fin 3 → ℝ) → ℂ} (n : Mode) :
    ‖cubeCoeff f n‖ ≤ ∫ x in Icc (0 : Fin 3 → ℝ) 1, ‖f x‖ := by
  rw [cubeCoeff_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; funext x; rw [norm_mul, norm_charK, mul_one]

/-- **Proved.** Fourier coefficients of the convective term of a smooth periodic slice. -/
lemma convective_coeff {v : VelocityField} (hv : IsPeriodicSmoothInitialData v) (k : Mode)
    (i : Fin 3) :
    ∑ l, cubeCoeff (fun x => liftR (fun y => v y l) x * liftR (pdR l (fun y => v y i)) x) k =
      2 * Real.pi * Complex.I * ∑' m : Mode,
        (∑ l, fourierCoeffVF v m l * ((((k - m) l : ℤ)) : ℂ)) * fourierCoeffVF v (k - m) i := by
  have hφ : ∀ l, PerR (fun y => v y l) := fun l => perR_coord hv.1 hv.2.2 l
  have hterm : ∀ l, cubeCoeff (fun x => liftR (fun y => v y l) x *
      liftR (pdR l (fun y => v y i)) x) k = ∑' m, fourierCoeffVF v m l *
        cubeCoeff (liftR (pdR l (fun y => v y i))) (k - m) := fun l =>
    cubeCoeff_mul_series ((hφ i).pdR l).continuous_liftR (summable_norm_fourierCoeffVF hv l)
      (fun x => by
        have := fourierCoeffVF_hasSum hv l ((Eq3).symm x)
        simpa [liftR] using this) k
  have hsum : ∀ l ∈ (Finset.univ : Finset (Fin 3)), Summable fun m => fourierCoeffVF v m l *
      cubeCoeff (liftR (pdR l (fun y => v y i))) (k - m) := by
    intro l _
    refine Summable.of_norm_bounded ((summable_norm_fourierCoeffVF hv l).mul_right
      (∫ x in Icc (0 : Fin 3 → ℝ) 1, ‖liftR (pdR l (fun y => v y i)) x‖)) fun m => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_cubeCoeff_le _) (norm_nonneg _)
  simp_rw [hterm]
  rw [← Summable.tsum_finsetSum hsum, ← tsum_mul_left]
  congr 1; funext m
  simp only [cubeCoeff_pdR (hφ i), ← compC_eq_liftR, ← fourierCoeffVF_eq_cubeCoeff,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  push_cast; ring

/-- **Proved.** Algebraic Leray step: if `w = -V a - π k - C` with `k·a = 0` and `k·w = 0`, then
`w = -V a - P_k C` (the pressure drops out). -/
lemma leray_solve (k : Mode) (a w C : Fin 3 → ℂ) (V π : ℂ)
    (hw : ∀ i, w i = -V * a i - π * (kvec k i : ℂ) - C i) (ha : dot (kvec k) a = 0)
    (hwd : dot (kvec k) w = 0) (i : Fin 3) : w i = -V * a i - lerayP k C i := by
  by_cases h : ksq (kvec k) = 0
  · have hk : ∀ j, kvec k j = 0 := by
      intro j
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (kvec k j))).1 h j
        (Finset.mem_univ j)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    rw [hw i]; simp [lerayP, hk]
  · have e : dot (kvec k) w = -V * dot (kvec k) a - π * (ksq (kvec k) : ℂ) - dot (kvec k) C := by
      simp only [dot, hw]
      rw [← dot_self_kvec]
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hwd, ha] at e
    have hk : (ksq (kvec k) : ℂ) ≠ 0 := by exact_mod_cast h
    have hπ : π = -dot (kvec k) C / (ksq (kvec k) : ℂ) := by
      field_simp; linear_combination e
    rw [hw i, hπ]; simp only [lerayP]; ring

/-- Coefficients of `∂ₜu` (coined). -/
def dtCoeff (T : ℝ) (u : TimeDependentVelocity) (t : ℝ) (k : Mode) : Fin 3 → ℂ := fun j =>
  cubeCoeff (liftR (fun y => Corrected.D T u (t, y) (1, 0) j)) k

lemma data_of_sol {ν : ℝ} {u₀ : VelocityField} {T : ℝ} {u : TimeDependentVelocity}
    {p : TimeDependentPressure} (hs : IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p)
    {τ : ℝ} (hτ : τ ∈ Icc 0 T) : IsPeriodicSmoothInitialData (u τ) :=
  ⟨Corrected.contDiff_slice hs.2.2.2.1 hτ, hs.2.2.2.2.2.2.1 τ hτ, hs.2.1 τ hτ⟩

/-- **Proved.** On `[0,T]`, if the coefficients of `∂ₜu` are orthogonal to `k`, they equal the
Fourier NS field (pressure removed by the Leray step). -/
lemma fourierNSField_eq_dtCoeff {ν : ℝ} {u₀ : VelocityField} {T : ℝ} {u : TimeDependentVelocity}
    {p : TimeDependentPressure} (hs : IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p)
    {t : ℝ} (hti : t ∈ Icc 0 T) (k : Mode) (hwd : dot (kvec k) (dtCoeff T u t k) = 0) (i : Fin 3) :
    fourierNSField ν (fourierCoeffVF (u t)) k i = dtCoeff T u t k i := by
  set a := fourierCoeffVF (u t)
  set C : Fin 3 → ℂ := fun j => 2 * Real.pi * Complex.I * ∑' m : Mode,
    (∑ l, a m l * ((((k - m) l : ℤ)) : ℂ)) * a (k - m) j
  have hw : ∀ j, dtCoeff T u t k j = -((viscCoeff ν k : ℝ) : ℂ) * a k j -
      (2 * Real.pi * Complex.I * cubeCoeff (liftR (p t)) k) * (kvec k j : ℂ) - C j := by
    intro j
    simp only [dtCoeff, C, a]
    rw [cubeCoeff_dt_eq hs hti k j, convective_coeff (data_of_sol hs hti) k j]
    have : (ν : ℂ) * ∑ l, (2 * Real.pi * Complex.I * ((k l : ℝ) : ℂ)) ^ 2 *
        fourierCoeffVF (u t) k j = -((viscCoeff ν k : ℝ) : ℂ) * fourierCoeffVF (u t) k j := by
      simp only [viscCoeff, ksq, kvec, mul_pow, Complex.I_sq, ← Finset.sum_mul, ← Finset.mul_sum]
      push_cast; ring
    rw [this]; simp only [kvec]; ring
  have hfin := leray_solve k (a k) _ C _ _ hw (periodicDataDivFree (u t) (data_of_sol hs hti) k)
    hwd i
  rw [hfin]; rfl

lemma dtCoeff_div_Ioo {ν : ℝ} {u₀ : VelocityField} {T : ℝ} {u : TimeDependentVelocity}
    {p : TimeDependentPressure} (hs : IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (k : Mode) : dot (kvec k) (dtCoeff T u t k) = 0 := by
  have hd : ∀ j, HasDerivAt (fun τ => fourierCoeffVF (u τ) k j) (dtCoeff T u t k j) t :=
    fun j => hasDerivAt_coeff_time hs.2.2.2.1 ht k j
  have h1 : HasDerivAt (fun τ => dot (kvec k) (fourierCoeffVF (u τ) k))
      (dot (kvec k) (dtCoeff T u t k)) t := by
    simp only [dot]
    exact HasDerivAt.fun_sum fun j _ => (hd j).const_mul _
  have h2 : (fun τ => dot (kvec k) (fourierCoeffVF (u τ) k)) =ᶠ[𝓝 t] fun _ => (0 : ℂ) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with τ hτ
    exact periodicDataDivFree (u τ) (data_of_sol hs hτ) k
  exact h1.unique ((hasDerivAt_const t (0 : ℂ)).congr_of_eventuallyEq h2)

/-- **Proved.** Discharges `PeriodicFourierCoeffODE ν`: on `(0, T')` the Fourier coefficients of a
classical periodic solution satisfy `û' = fourierNSField ν û`. -/
theorem periodicFourierCoeffODE (ν : ℝ) : PeriodicFourierCoeffODE ν := by
  intro _ u₀ u p T' hs t ht k i
  have hu := hs.2.2.2.1
  have hti : t ∈ Icc 0 T' := Ioo_subset_Icc_self ht
  have hd : ∀ j, HasDerivAt (fun τ => fourierCoeffVF (u τ) k j) (dtCoeff T' u t k j) t :=
    fun j => hasDerivAt_coeff_time hu ht k j
  have hwd : dot (kvec k) (dtCoeff T' u t k) = 0 := by
    have h1 : HasDerivAt (fun τ => dot (kvec k) (fourierCoeffVF (u τ) k))
        (dot (kvec k) (dtCoeff T' u t k)) t := by
      simp only [dot]
      exact HasDerivAt.fun_sum fun j _ => (hd j).const_mul _
    have h2 : (fun τ => dot (kvec k) (fourierCoeffVF (u τ) k)) =ᶠ[𝓝 t] fun _ => (0 : ℂ) := by
      filter_upwards [Icc_mem_nhds ht.1 ht.2] with τ hτ
      exact periodicDataDivFree (u τ) (data_of_sol hs hτ) k
    exact h1.unique ((hasDerivAt_const t (0 : ℂ)).congr_of_eventuallyEq h2)
  rw [fourierNSField_eq_dtCoeff hs hti k hwd i]; exact hd i

/-! ### Uniform-in-time rapid decay -/

/-- Spatial partial derivative of a space-time scalar field, within `[0,T] × ℝ³` (coined). -/
def dJ (T : ℝ) (j : Fin 3) (W : ℝ × T3 → ℝ) : ℝ × T3 → ℝ := fun q =>
  fderivWithin ℝ W (Corrected.S T) q ((0 : ℝ), EuclideanSpace.single j 1)

/-- `1 - Δ/(4π²)` on scalar fields (coined). -/
def helmR (φ : T3 → ℝ) : T3 → ℝ := fun y =>
  φ y - (4 * Real.pi ^ 2)⁻¹ * ∑ j, pdR j (pdR j φ) y

/-- Space-time version of `helmR` (coined). -/
def helmJ (T : ℝ) (W : ℝ × T3 → ℝ) : ℝ × T3 → ℝ := fun q =>
  W q - (4 * Real.pi ^ 2)⁻¹ * ∑ j, dJ T j (dJ T j W) q

/-- Smooth on `[0,T] × ℝ³` with `1`-periodic time slices (coined). -/
def JReg (T : ℝ) (W : ℝ × T3 → ℝ) : Prop :=
  ContDiffOn ℝ ∞ W (Corrected.S T) ∧
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x j, W (t, x + EuclideanSpace.single j 1) = W (t, x)

lemma PerR.helmR {φ : T3 → ℝ} (h : PerR φ) : PerR (helmR φ) := by
  refine ⟨h.1.sub (contDiff_const.mul (ContDiff.sum fun j _ => ((h.pdR j).pdR j).1)),
    fun x m => ?_⟩
  simp only [PeriodicNSContinuation.helmR, h.2 x m, fun j => ((h.pdR j).pdR j).2 x m]

lemma cubeCoeff_helmR {φ : T3 → ℝ} (h : PerR φ) (k : Mode) :
    cubeCoeff (liftR (helmR φ)) k = ((1 + ∑ j, ((k j : ℝ)) ^ 2 : ℝ) : ℂ) * cubeCoeff (liftR φ) k := by
  have c2 : ∀ j, Continuous (liftR (pdR j (pdR j φ))) := fun j =>
    ((h.pdR j).pdR j).continuous_liftR
  have e : liftR (helmR φ) = fun x => liftR φ x -
      (((4 * Real.pi ^ 2)⁻¹ : ℝ) : ℂ) * ∑ j, liftR (pdR j (pdR j φ)) x := by
    funext x; simp only [liftR, PeriodicNSContinuation.helmR]; push_cast; rfl
  rw [e, cubeCoeff_sub' (f := liftR φ)
      (g := fun x => (((4 * Real.pi ^ 2)⁻¹ : ℝ) : ℂ) * ∑ j, liftR (pdR j (pdR j φ)) x)
      h.continuous_liftR (continuous_const.mul (continuous_finset_sum _ fun j _ => c2 j)),
    cubeCoeff_const_mul' _ (fun x => ∑ j, liftR (pdR j (pdR j φ)) x), cubeCoeff_sum' c2]
  have hj : ∀ j, cubeCoeff (liftR (pdR j (pdR j φ))) k =
      -(4 * (Real.pi : ℂ) ^ 2) * (((k j : ℝ)) ^ 2 : ℝ) * cubeCoeff (liftR φ) k := by
    intro j
    rw [cubeCoeff_pdR (h.pdR j) j k, cubeCoeff_pdR h j k]
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [Finset.sum_congr rfl fun j _ => hj j, ← Finset.sum_mul, ← Finset.mul_sum]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring

variable {T : ℝ}

lemma JReg.slice {W : ℝ × T3 → ℝ} (h : JReg T W) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    PerR (fun y => W (t, y)) :=
  ⟨h.1.comp_contDiff (f := fun x : T3 => (t, x)) (contDiff_const.prodMk contDiff_id)
    (fun _ => ⟨ht, trivial⟩), fun x j => h.2 t ht x j⟩

lemma pdR_slice {W : ℝ × T3 → ℝ} (hW : ContDiffOn ℝ ∞ W (Corrected.S T)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) (j : Fin 3) :
    pdR j (fun y => W (t, y)) = fun y => dJ T j W (t, y) := by
  funext y
  have hd : HasFDerivWithinAt W (fderivWithin ℝ W (Corrected.S T) (t, y)) (Corrected.S T) (t, y) :=
    ((hW.differentiableOn (by simp)) (t, y) ⟨ht, trivial⟩).hasFDerivWithinAt
  have h1 : HasFDerivAt (fun x : T3 => (t, x)) (ContinuousLinearMap.inr ℝ ℝ T3) y :=
    (hasFDerivAt_const t y).prodMk (hasFDerivAt_id y)
  have := hd.comp y h1.hasFDerivWithinAt (s := univ) (fun _ _ => ⟨ht, trivial⟩)
  simp only [PeriodicNSContinuation.pdR, dJ]
  rw [show (fun y => W (t, y)) = W ∘ (fun x : T3 => (t, x)) from rfl,
    (this.hasFDerivAt Filter.univ_mem).fderiv]
  simp

lemma JReg.dJ (hT : 0 < T) {W : ℝ × T3 → ℝ} (h : JReg T W) (j : Fin 3) : JReg T (dJ T j W) := by
  refine ⟨((h.1.fderivWithin (Corrected.uniqueDiffOn_S hT) (m := ∞) le_rfl).clm_apply
    contDiffOn_const), fun t ht x m => ?_⟩
  have e := congrFun (pdR_slice h.1 ht j)
  rw [← e, ← e]; exact ((h.slice ht).pdR j).2 x m

lemma JReg.helm (hT : 0 < T) {W : ℝ × T3 → ℝ} (h : JReg T W) : JReg T (helmJ T W) := by
  refine ⟨h.1.sub (contDiffOn_const.mul (ContDiffOn.sum fun j _ => ((h.dJ hT j).dJ hT j).1)),
    fun t ht x m => ?_⟩
  simp only [PeriodicNSContinuation.helmJ, h.2 t ht x m, fun j => ((h.dJ hT j).dJ hT j).2 t ht x m]

lemma helmR_slice (hT : 0 < T) {W : ℝ × T3 → ℝ} (h : JReg T W) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    helmR (fun y => W (t, y)) = fun y => helmJ T W (t, y) := by
  funext y
  simp only [PeriodicNSContinuation.helmR, PeriodicNSContinuation.helmJ, pdR_slice h.1 ht,
    pdR_slice (h.dJ hT _).1 ht]

lemma JReg.iterate (hT : 0 < T) {W : ℝ × T3 → ℝ} (h : JReg T W) (m : ℕ) :
    JReg T ((helmJ T)^[m] W) := by
  induction m with
  | zero => exact h
  | succ m ih => rw [Function.iterate_succ_apply']; exact ih.helm hT

lemma cubeCoeff_iterate_helmJ (hT : 0 < T) {W : ℝ × T3 → ℝ} (h : JReg T W) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) (m : ℕ) (k : Mode) :
    cubeCoeff (liftR (fun y => (helmJ T)^[m] W (t, y))) k =
      ((1 + ∑ j, ((k j : ℝ)) ^ 2 : ℝ) : ℂ) ^ m * cubeCoeff (liftR (fun y => W (t, y))) k := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hm := h.iterate hT m
    rw [Function.iterate_succ_apply', ← helmR_slice hT hm ht, cubeCoeff_helmR (hm.slice ht), ih]
    ring

/-- **Proved.** Uniform-in-time rapid decay of the cube coefficients of the slices of a smooth
space-time field with periodic slices. -/
theorem jreg_decay (hT : 0 < T) {W : ℝ × T3 → ℝ} (h : JReg T W) (r : ℝ) :
    ∃ B, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ k,
      ‖cubeCoeff (liftR (fun y => W (t, y))) k‖ ≤ B * sobW (-r) k := by
  set m : ℕ := ⌈max r 0⌉₊
  set K : Set (ℝ × T3) := Icc (0 : ℝ) T ×ˢ ((Eq3).symm '' Icc (0 : Fin 3 → ℝ) 1)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.image (Eq3).symm.continuous)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((h.iterate hT m).1.continuousOn.mono fun q hq => ⟨hq.1, trivial⟩)
  refine ⟨max C 0, le_max_right _ _, fun t ht k => ?_⟩
  have hvol : (volume (Icc (0 : Fin 3 → ℝ) 1)) = 1 := by simp [Real.volume_Icc_pi]
  have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (0 : Fin 3 → ℝ) 1)
    (f := fun x => liftR (fun y => (helmJ T)^[m] W (t, y)) x * charK k x) (C := max C 0)
    (by rw [hvol]; simp) (fun x hx => by
      rw [norm_mul, norm_charK, mul_one]
      have := hC (t, (Eq3).symm x) ⟨ht, x, hx, rfl⟩
      simp only [liftR, Complex.norm_real]
      exact this.trans (le_max_left _ _))
  rw [Measure.real, hvol] at hb
  simp only [ENNReal.toReal_one, mul_one] at hb
  rw [← cubeCoeff_eq, cubeCoeff_iterate_helmJ hT h ht, norm_mul, norm_pow] at hb
  set w : ℝ := 1 + ∑ j, ((k j : ℝ)) ^ 2
  have hw1 : 1 ≤ w := by simp only [w]; have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) =>
    sq_nonneg ((k j : ℝ))); linarith
  have hw : 0 < w := by linarith
  rw [Complex.norm_of_nonneg hw.le] at hb
  have hwm : 0 < w ^ m := pow_pos hw m
  have h1 : ‖cubeCoeff (liftR (fun y => W (t, y))) k‖ ≤ max C 0 * (w ^ m)⁻¹ := by
    rw [le_mul_inv_iff₀ hwm]; linarith
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (le_max_right _ _))
  unfold sobW
  rw [← Real.rpow_natCast, ← Real.rpow_neg hw.le]
  refine Real.rpow_le_rpow_of_exponent_le hw1 ?_
  have := Nat.le_ceil (max r 0); have := le_max_left r 0; simp only [m] at *; linarith

lemma JReg.continuousOn_coeff (hT : 0 < T) {W : ℝ × T3 → ℝ} (h : JReg T W) (k : Mode) :
    ContinuousOn (fun t => cubeCoeff (liftR (fun y => W (t, y))) k) (Icc 0 T) := by
  set pr : ℝ → ℝ := fun t => (projIcc 0 T hT.le t : ℝ)
  have hpr : Continuous pr := continuous_subtype_val.comp continuous_projIcc
  have hjoint : Continuous fun q : ℝ × T3 => W (pr q.1, q.2) := by
    refine h.1.continuousOn.comp_continuous ((hpr.comp continuous_fst).prodMk continuous_snd)
      fun q => ?_
    exact ⟨(projIcc 0 T hT.le q.1).2, mem_univ _⟩
  set F : ℝ → (Fin 3 → ℝ) → ℂ := fun t x => ((W (pr t, (Eq3).symm x) : ℝ) : ℂ) * charK k x
  have hF : Continuous (Function.uncurry F) :=
    (Complex.continuous_ofReal.comp (hjoint.comp (continuous_fst.prodMk
      ((Eq3).symm.continuous.comp continuous_snd)))).mul
      ((charK_contDiff k (n := 0)).continuous.comp continuous_snd)
  have hint : Continuous fun t => ∫ x in Icc (0 : Fin 3 → ℝ) 1, F t x :=
    continuous_parametric_integral_of_continuous hF isCompact_Icc
  refine hint.continuousOn.congr fun t ht => ?_
  simp only [cubeCoeff_eq, F, pr, projIcc_of_mem hT.le ht, liftR]

section solution
variable {ν : ℝ} {u₀ : VelocityField} {u : TimeDependentVelocity} {p : TimeDependentPressure}

lemma jreg_u (hs : IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p) (i : Fin 3) :
    JReg T (fun q => u q.1 q.2 i) :=
  ⟨(EuclideanSpace.proj i : T3 →L[ℝ] ℝ).contDiff.comp_contDiffOn hs.2.2.2.1,
    fun t ht x j => (perR_coord (Corrected.contDiff_slice hs.2.2.2.1 ht) (hs.2.1 t ht) i).2 x j⟩

lemma jreg_dt (hs : IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p) (i : Fin 3) :
    JReg T (fun q => Corrected.D T u q (1, 0) i) := by
  have hT := hs.1
  have hu := hs.2.2.2.1
  refine ⟨(EuclideanSpace.proj i : T3 →L[ℝ] ℝ).contDiff.comp_contDiffOn
    ((hu.fderivWithin (Corrected.uniqueDiffOn_S hT) (m := ∞) le_rfl).clm_apply
      contDiffOn_const), fun t ht x j => ?_⟩
  have e : (fun s => u s (x + EuclideanSpace.single j 1)) =ᶠ[𝓝[Icc 0 T] t] fun s => u s x := by
    filter_upwards [self_mem_nhdsWithin] with s hs'
    simp only [show (EuclideanSpace.single j (1 : ℝ) : T3) = stdBasisVec j from rfl,
      (isZ3Periodic_iff_unit_shifts (u s)).1 (hs.2.1 s hs')]
  have e2 := e.derivWithin_eq (by
    simp only [show (EuclideanSpace.single j (1 : ℝ) : T3) = stdBasisVec j from rfl,
      (isZ3Periodic_iff_unit_shifts (u t)).1 (hs.2.1 t ht)])
  rw [Corrected.derivWithin_time hu hT ht, Corrected.derivWithin_time hu hT ht] at e2
  simp only [e2]

/-- **Proved.** The divergence constraint on `∂ₜû` extends to the closed interval by continuity. -/
lemma dtCoeff_div (hs : IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p)
    {t : ℝ} (ht : t ∈ Icc 0 T) (k : Mode) : dot (kvec k) (dtCoeff T u t k) = 0 := by
  have hT := hs.1
  have hc : ContinuousOn (fun τ => dot (kvec k) (dtCoeff T u τ k)) (Icc 0 T) := by
    simp only [dot]
    exact continuousOn_finset_sum _ fun j _ =>
      continuousOn_const.mul ((jreg_dt hs j).continuousOn_coeff hT k)
  have := Set.EqOn.of_subset_closure (f := fun τ => dot (kvec k) (dtCoeff T u τ k))
    (g := fun _ => (0 : ℂ)) (s := Ioo 0 T) (t := Icc 0 T)
    (fun τ hτ => dtCoeff_div_Ioo hs hτ k) hc continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo hT.ne])
  exact this ht

end solution

/-- **Proved.** Discharges `PeriodicFourierCoeffDecay ν`: uniform-in-time rapid decay of `û(t)`
and of `fourierNSField ν û(t)` on `[0, T']`. -/
theorem periodicFourierCoeffDecay (ν : ℝ) : PeriodicFourierCoeffDecay ν := by
  intro _ u₀ u p T' hs r
  have hT := hs.1
  choose B1 hB1 h1 using fun i => jreg_decay hT (jreg_u hs i) r
  choose B2 hB2 h2 using fun i => jreg_decay hT (jreg_dt hs i) r
  refine ⟨∑ i, (B1 i + B2 i), Finset.sum_nonneg fun i _ => add_nonneg (hB1 i) (hB2 i),
    fun t ht k i => ⟨?_, ?_⟩⟩
  · have hle : B1 i ≤ ∑ i, (B1 i + B2 i) :=
      (le_add_of_nonneg_right (hB2 i)).trans (Finset.single_le_sum (f := fun i => B1 i + B2 i)
        (fun i _ => add_nonneg (hB1 i) (hB2 i)) (Finset.mem_univ i))
    exact (h1 i t ht k).trans (mul_le_mul_of_nonneg_right hle (sobW_pos _ _).le)
  · have hle : B2 i ≤ ∑ i, (B1 i + B2 i) :=
      (le_add_of_nonneg_left (hB1 i)).trans (Finset.single_le_sum (f := fun i => B1 i + B2 i)
        (fun i _ => add_nonneg (hB1 i) (hB2 i)) (Finset.mem_univ i))
    rw [fourierNSField_eq_dtCoeff hs ht k (dtCoeff_div hs ht k) i]
    exact (h2 i t ht k).trans (mul_le_mul_of_nonneg_right hle (sobW_pos _ _).le)

/-- **Proved, unconditionally.** The periodic Fourier `H^s` energy identity. -/
theorem periodicFourierHsEnergyIdentity (ν s : ℝ) : PeriodicFourierHsEnergyIdentity ν s :=
  periodicFourierHsEnergyIdentity_of_coeff (s := s) (periodicFourierCoeffODE ν) (periodicFourierCoeffDecay ν)

/-- **Proved (conditional on the commutator and low-frequency Props only).** -/
theorem periodicBKMHsControl_of_commutator_lowFreq {s : ℝ} (ν : ℝ) (hs : 5 / 2 < s)
    (hC : ∃ C, 0 ≤ C ∧ PeriodicFourierCommutatorBound s C)
    (hL : PeriodicLowFreqVorticityBound) : PeriodicBKMHsControl ν s :=
  periodicBKMHsControl_of_coeff_lowFreq ν hs periodicFourierCoeffODE periodicFourierCoeffDecay hC hL

end PeriodicNSContinuation
