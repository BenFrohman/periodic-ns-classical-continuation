/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.CoeffODE
import PeriodicNSContinuation.Parseval

/-!
# Physical-space form of the `s = 3` commutator bound
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D TorusFourierNS
open scoped ContDiff

namespace PeriodicNSContinuation

local notation "Eq3" => EuclideanSpace.equiv (Fin 3) ℝ

lemma PerR.add_int {φ : T3 → ℝ} (h : PerR φ) (y : T3) (j : Fin 3) (n : ℤ) :
    φ (y + (n : ℝ) • EuclideanSpace.single j 1) = φ y := by
  have step : ∀ r : ℝ, φ (y + (r + 1) • EuclideanSpace.single j 1) =
      φ (y + r • EuclideanSpace.single j 1) := fun r => by
    rw [add_smul, one_smul, ← add_assoc, h.2]
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih => rw [show (((n : ℤ) + 1 : ℤ) : ℝ) = ((n : ℤ) : ℝ) + 1 by push_cast; ring, step, ih]
  | pred n ih =>
    rw [← ih, ← step]; congr 3; push_cast; ring

lemma PerR.liftR_int {φ : T3 → ℝ} (h : PerR φ) (y : Fin 3 → ℝ) (n : Fin 3 → ℤ) :
    liftR φ (y + fun j => (n j : ℝ)) = liftR φ y := by
  have e : (Eq3).symm (y + fun j => (n j : ℝ)) = (Eq3).symm y +
      (((n 0 : ℝ) • EuclideanSpace.single 0 1 + (n 1 : ℝ) • EuclideanSpace.single 1 1) +
        (n 2 : ℝ) • EuclideanSpace.single 2 1) := by
    ext j; fin_cases j <;> simp
  simp only [liftR, e, ← add_assoc, h.add_int]

lemma PerR.iterate_helmR {φ : T3 → ℝ} (h : PerR φ) (m : ℕ) : PerR (PeriodicNSContinuation.helmR^[m] φ) := by
  induction m with
  | zero => exact h
  | succ m ih => rw [Function.iterate_succ_apply']; exact ih.helmR

lemma cubeCoeff_iterate_helmR {φ : T3 → ℝ} (h : PerR φ) (m : ℕ) (k : Mode) :
    cubeCoeff (liftR (PeriodicNSContinuation.helmR^[m] φ)) k =
      (((1 + ∑ j, ((k j : ℝ)) ^ 2) ^ m : ℝ) : ℂ) * cubeCoeff (liftR φ) k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', cubeCoeff_helmR (h.iterate_helmR m), ih]
    push_cast; ring


/-- Fiberwise assembly of a `HasSum` over `Mode × Fin 3`. -/
lemma hasSum_mode_fin {g : Mode × Fin 3 → ℝ} {c : Fin 3 → ℝ}
    (h : ∀ i, HasSum (fun k => g (k, i)) (c i)) : HasSum g (∑ i, c i) := by
  have e : g = fun p => ∑ i, if p.2 = i then g p else 0 := by
    funext p; simp
  rw [e]
  refine hasSum_sum fun i _ => ?_
  have hinj : Function.Injective (fun k : Mode => (k, i)) := fun a b hab => by
    simpa using congrArg Prod.fst hab
  refine (hinj.hasSum_iff fun p hp => ?_).1 ?_
  · rw [if_neg]; rintro rfl; exact hp ⟨p.1, rfl⟩
  · simpa [Function.comp_def] using h i

/-- The convective term `((v·∇)v)_i` as a real scalar field (coined). -/
def convR (v : VelocityField) (i : Fin 3) : T3 → ℝ := fun y =>
  ∑ l, v y l * pdR l (fun y => v y i) y

lemma perR_convR {v : VelocityField} (hv : IsPeriodicSmoothInitialData v) (i : Fin 3) :
    PerR (convR v i) := by
  have hφ : ∀ l, PerR (fun y => v y l) := fun l => perR_coord hv.1 hv.2.2 l
  refine ⟨ContDiff.sum fun l _ => (hφ l).1.mul ((hφ i).pdR l).1, fun x j => ?_⟩
  simp only [convR, (hφ _).2 x j, ((hφ i).pdR _).2 x j]

lemma cubeCoeff_convR {v : VelocityField} (hv : IsPeriodicSmoothInitialData v) (k : Mode)
    (i : Fin 3) : cubeCoeff (liftR (convR v i)) k =
      2 * Real.pi * Complex.I * ∑' m : Mode,
        (∑ l, fourierCoeffVF v m l * ((((k - m) l : ℤ)) : ℂ)) * fourierCoeffVF v (k - m) i := by
  have hφ : ∀ l, PerR (fun y => v y l) := fun l => perR_coord hv.1 hv.2.2 l
  have e : liftR (convR v i) = fun x => ∑ l, (fun l x => liftR (fun y => v y l) x *
      liftR (pdR l (fun y => v y i)) x) l x := by
    funext x; simp only [liftR, convR]; push_cast; rfl
  rw [e, cubeCoeff_sum' (f := fun l x => liftR (fun y => v y l) x *
      liftR (pdR l (fun y => v y i)) x)
      fun l => (hφ l).continuous_liftR.mul ((hφ i).pdR l).continuous_liftR]
  exact convective_coeff hv k i

lemma nlField_eq_convR {v : VelocityField} (hv : IsPeriodicSmoothInitialData v) (k : Mode)
    (i : Fin 3) : nlField (fourierCoeffVF v) k i =
      -lerayP k (fun j => cubeCoeff (liftR (convR v j)) k) i := by
  simp only [nlField, fourierNSField, viscCoeff, cubeCoeff_convR hv]
  simp


lemma abs_mul_le_ksq (k : Mode) (i j : Fin 3) : |kvec k i| * |kvec k j| ≤ ksq (kvec k) := by
  have hi : kvec k i ^ 2 ≤ ksq (kvec k) :=
    Finset.single_le_sum (f := fun j => kvec k j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hj : kvec k j ^ 2 ≤ ksq (kvec k) :=
    Finset.single_le_sum (f := fun j => kvec k j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ j)
  nlinarith [sq_abs (kvec k i), sq_abs (kvec k j), sq_nonneg (|kvec k i| - |kvec k j|)]

/-- The gradient (pressure) part of the Leray projection is controlled by `‖H‖² + ‖W‖²`. -/
lemma leray_grad_term_bound (k : Mode) (H W : Fin 3 → ℂ) (i : Fin 3) :
    |2 * ((starRingEnd ℂ) (H i) * (dot (kvec k) W / (ksq (kvec k) : ℂ) * (kvec k i : ℂ))).re| ≤
      ∑ j, (‖H i‖ ^ 2 + ‖W j‖ ^ 2) := by
  have hnn : 0 ≤ ∑ j, (‖H i‖ ^ 2 + ‖W j‖ ^ 2) := Finset.sum_nonneg fun _ _ => by positivity
  by_cases h0 : ksq (kvec k) = 0
  · simp [h0, hnn]
  have hpos : 0 < ksq (kvec k) :=
    lt_of_le_of_ne (Finset.sum_nonneg fun j _ => sq_nonneg _) (Ne.symm h0)
  have hdot : ‖dot (kvec k) W‖ ≤ ∑ j, |kvec k j| * ‖W j‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hkey : ‖dot (kvec k) W‖ * |kvec k i| ≤ ksq (kvec k) * ∑ j, ‖W j‖ := by
    calc ‖dot (kvec k) W‖ * |kvec k i| ≤ (∑ j, |kvec k j| * ‖W j‖) * |kvec k i| :=
          mul_le_mul_of_nonneg_right hdot (abs_nonneg _)
      _ = ∑ j, (|kvec k i| * |kvec k j|) * ‖W j‖ := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => by ring
      _ ≤ ∑ j, ksq (kvec k) * ‖W j‖ :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_right (abs_mul_le_ksq k i j) (norm_nonneg _)
      _ = _ := by rw [Finset.mul_sum]
  have hz : ‖(starRingEnd ℂ) (H i) * (dot (kvec k) W / (ksq (kvec k) : ℂ) * (kvec k i : ℂ))‖ ≤
      ‖H i‖ * ∑ j, ‖W j‖ := by
    rw [norm_mul, norm_mul, norm_div, Complex.norm_conj, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]; linarith
  rw [abs_mul, abs_two]
  calc 2 * |_| ≤ 2 * (‖H i‖ * ∑ j, ‖W j‖) :=
        mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hz) (by norm_num)
    _ = ∑ j, 2 * ‖H i‖ * ‖W j‖ := by rw [Finset.mul_sum, Finset.mul_sum]; ring_nf
    _ ≤ _ := Finset.sum_le_sum fun j _ => by nlinarith [sq_nonneg (‖H i‖ - ‖W j‖)]


/-- Parseval for real smooth periodic scalar fields. -/
lemma hasSum_re_cubeCoeff {φ ψ : T3 → ℝ} (hφ : PerR φ) (hψ : PerR ψ) :
    HasSum (fun k => ((starRingEnd ℂ) (cubeCoeff (liftR φ) k) * cubeCoeff (liftR ψ) k).re)
      (∫ x in Icc (0 : Fin 3 → ℝ) 1, φ ((Eq3).symm x) * ψ ((Eq3).symm x)) := by
  have h := Complex.reCLM.hasSum (hasSum_prod_cubeCoeff hφ.continuous_liftR hψ.continuous_liftR
    hφ.liftR_int hψ.liftR_int)
  have e : (fun x => (starRingEnd ℂ) (liftR φ x) * liftR ψ x) =
      fun x => ((φ ((Eq3).symm x) * ψ ((Eq3).symm x) : ℝ) : ℂ) := by
    funext x; simp [liftR]
  rw [e, integral_complex_ofReal] at h
  simpa using h

lemma summable_sq_norm_cubeCoeff {φ : T3 → ℝ} (hφ : PerR φ) :
    Summable (fun k => ‖cubeCoeff (liftR φ) k‖ ^ 2) := by
  refine (hasSum_re_cubeCoeff hφ hφ).summable.congr fun k => ?_
  rw [Complex.conj_mul']; norm_cast


/-- Coined. **Stated here; proved in `CommutatorAssembly.lean`** (`periodicPhysicalCommutatorBound`). Physical-space `s = 3` commutator bound:
`-2 ∑ᵢ ∫_{[0,1]³} (1 - Δ/4π²)³vᵢ · ((v·∇)v)ᵢ ≤ C ‖∇v‖_∞ ‖v‖²_{H³}`. Only the convective term
appears; the pressure has been removed by `k · v̂ = 0` (see
`periodicFourierCommutatorBound_of_physical`). -/
def PeriodicPhysicalCommutatorBound (C : ℝ) : Prop :=
  ∀ v : VelocityField, IsPeriodicSmoothInitialData v →
    -2 * ∑ i, ∫ x in Icc (0 : Fin 3 → ℝ) 1,
      (PeriodicNSContinuation.helmR^[3] (fun y => v y i)) ((Eq3).symm x) * convR v i ((Eq3).symm x)
      ≤ C * gradSupNorm v * hsSq 3 v

/-- **Proved.** The Fourier-side `H³` nonlinear rate is summable and equals the physical-space
pairing `-2 ∑ᵢ ∫ (1 - Δ/4π²)³vᵢ · ((v·∇)v)ᵢ`. -/
theorem hasSum_rate_three {v : VelocityField} (hv : IsPeriodicSmoothInitialData v) :
    HasSum (fun p : Mode × Fin 3 => sobW 3 p.1 *
        (2 * ((starRingEnd ℂ) (fourierCoeffVF v p.1 p.2) * nlField (fourierCoeffVF v) p.1 p.2).re))
      (-2 * ∑ i, ∫ x in Icc (0 : Fin 3 → ℝ) 1,
        (PeriodicNSContinuation.helmR^[3] (fun y => v y i)) ((Eq3).symm x) *
          convR v i ((Eq3).symm x)) := by
  set a := fourierCoeffVF v
  have hφ : ∀ i, PerR (fun y => v y i) := fun i => perR_coord hv.1 hv.2.2 i
  have hH : ∀ i, PerR (PeriodicNSContinuation.helmR^[3] (fun y => v y i)) := fun i =>
    (hφ i).iterate_helmR 3
  have hN : ∀ i, PerR (convR v i) := perR_convR hv
  set Hh : Mode → Fin 3 → ℂ := fun k i =>
    cubeCoeff (liftR (PeriodicNSContinuation.helmR^[3] (fun y => v y i))) k with hHh_def
  set W : Mode → Fin 3 → ℂ := fun k j => cubeCoeff (liftR (convR v j)) k with hW_def
  have hHh : ∀ k i, Hh k i = ((sobW 3 k : ℝ) : ℂ) * a k i := fun k i => by
    simp only [Hh, cubeCoeff_iterate_helmR (hφ i), a, fourierCoeffVF_eq_cubeCoeff, compC_eq_liftR]
    rw [show sobW 3 k = (1 + ∑ j, ((k j : ℝ)) ^ 2) ^ 3 by
      rw [sobW, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]]
  set A : Mode → Fin 3 → ℝ := fun k i => -2 * ((starRingEnd ℂ) (Hh k i) * W k i).re
  set B : Mode → Fin 3 → ℝ := fun k i => 2 * ((starRingEnd ℂ) (Hh k i) *
    (dot (kvec k) (W k) / (ksq (kvec k) : ℂ) * (kvec k i : ℂ))).re
  have hterm : ∀ k i, sobW 3 k * (2 * ((starRingEnd ℂ) (a k i) * nlField a k i).re) =
      A k i + B k i := fun k i => by
    have e : (starRingEnd ℂ) (Hh k i) = ((sobW 3 k : ℝ) : ℂ) * (starRingEnd ℂ) (a k i) := by
      rw [hHh, map_mul, Complex.conj_ofReal]
    simp only [A, B, e]
    rw [show nlField a k i = -lerayP k (W k) i from nlField_eq_convR hv k i]
    simp only [lerayP, mul_assoc, Complex.re_ofReal_mul, mul_neg, sub_eq_add_neg, mul_add,
      Complex.add_re, Complex.neg_re]
    ring
  have hdiv : ∀ k, ∑ i, (starRingEnd ℂ) (Hh k i) * (kvec k i : ℂ) = 0 := fun k => by
    have h0 := periodicDataDivFree v hv k
    have : ∑ i, (starRingEnd ℂ) (Hh k i) * (kvec k i : ℂ) =
        (starRingEnd ℂ) (((sobW 3 k : ℝ) : ℂ) * dot (kvec k) (a k)) := by
      simp only [hHh, dot, Finset.mul_sum, map_sum, map_mul, Complex.conj_ofReal]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [this, h0, mul_zero, map_zero]
  have hBsum : ∀ k, ∑ i, B k i = 0 := fun k => by
    simp only [B]
    rw [← Finset.mul_sum, ← Complex.re_sum]
    have : ∑ i, (starRingEnd ℂ) (Hh k i) *
        (dot (kvec k) (W k) / (ksq (kvec k) : ℂ) * (kvec k i : ℂ)) =
        dot (kvec k) (W k) / (ksq (kvec k) : ℂ) *
          ∑ i, (starRingEnd ℂ) (Hh k i) * (kvec k i : ℂ) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
    rw [this, hdiv]; simp
  have hAs : ∀ i, HasSum (fun k => A k i) (-2 * ∫ x in Icc (0 : Fin 3 → ℝ) 1,
      (PeriodicNSContinuation.helmR^[3] (fun y => v y i)) ((Eq3).symm x) *
        convR v i ((Eq3).symm x)) := fun i =>
    (hasSum_re_cubeCoeff (hH i) (hN i)).mul_left (-2)
  have hBs : ∀ i, Summable (fun k => B k i) := fun i =>
    Summable.of_norm_bounded (summable_sum fun j _ =>
      (summable_sq_norm_cubeCoeff (hH i)).add (summable_sq_norm_cubeCoeff (hN j)))
      fun k => by rw [Real.norm_eq_abs]; exact leray_grad_term_bound k (Hh k) (W k) i
  have hB : HasSum (fun p : Mode × Fin 3 => B p.1 p.2) 0 := by
    have := hasSum_mode_fin (g := fun p : Mode × Fin 3 => B p.1 p.2) fun i => (hBs i).hasSum
    rwa [← Summable.tsum_finsetSum fun i _ => hBs i, show (fun k => ∑ i, B k i) = fun _ => 0 from
      funext hBsum, tsum_zero] at this
  have hA := hasSum_mode_fin (g := fun p : Mode × Fin 3 => A p.1 p.2) hAs
  rw [Finset.mul_sum, ← add_zero (∑ i, _)]
  refine (hA.add hB).congr_fun fun p => ?_
  exact hterm p.1 p.2

/-- **Proved.** The physical-space bound implies the Fourier commutator bound at `s = 3`. -/
theorem periodicFourierCommutatorBound_of_physical {C : ℝ}
    (hP : PeriodicPhysicalCommutatorBound C) : PeriodicFourierCommutatorBound 3 C := fun v hv =>
  ⟨(hasSum_rate_three hv).summable, by rw [rateOf, (hasSum_rate_three hv).tsum_eq]; exact hP v hv⟩

/-- **Proved (conditional on `PeriodicPhysicalCommutatorBound` and
`PeriodicLowFreqVorticityBound`).** -/
theorem periodicBKMHsControl_of_physical_lowFreq (ν : ℝ)
    (hP : ∃ C, 0 ≤ C ∧ PeriodicPhysicalCommutatorBound C)
    (hL : PeriodicLowFreqVorticityBound) : PeriodicBKMHsControl ν 3 := by
  obtain ⟨C, hC0, hC⟩ := hP
  exact periodicBKMHsControl_of_commutator_lowFreq ν (by norm_num)
    ⟨C, hC0, periodicFourierCommutatorBound_of_physical hC⟩ hL

end PeriodicNSContinuation
