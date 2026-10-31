/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.SpatialSeries

/-!
# Calculus of vector Fourier series: Laplacian, gradient, convective term

All names here are coined.
-/

noncomputable section
open Set Filter Topology MeasureTheory NavierStokes3D FeffermanClayNS
open scoped ContDiff

namespace PeriodicNSContinuation

open TorusFourierNS (Mode FField)

/-- Vector series with componentwise coefficients, real part (coined). -/
def vecS (c : Fin 3 → Mode → ℂ) (y : T3) : EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm fun j => (seriesC (c j) y).re

lemma vecS_apply (c : Fin 3 → Mode → ℂ) (y : T3) (j : Fin 3) :
    vecS c y j = (seriesC (c j) y).re := rfl

lemma seriesVelocity_eq_vecS (a : ℝ → FField) (t : ℝ) :
    seriesVelocity a t = vecS (fun j n => a t n j) := rfl

lemma hasFDerivAt_vecS {c : Fin 3 → Mode → ℂ} (hc : ∀ j, HS 1 (c j)) (x : T3) :
    HasFDerivAt (vecS c) ((EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun j => Complex.reCLM.comp (fderiv ℝ (seriesC (c j)) x))) x := by
  have h : HasFDerivAt (fun y => fun j => (seriesC (c j) y).re)
      (ContinuousLinearMap.pi fun j => Complex.reCLM.comp (fderiv ℝ (seriesC (c j)) x)) x :=
    hasFDerivAt_pi.2 fun j => hasFDerivAt_re_seriesC (hc j) x
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.hasFDerivAt.comp x h

lemma fderiv_vecS_apply {c : Fin 3 → Mode → ℂ} (hc : ∀ j, HS 1 (c j)) (x v : T3) :
    fderiv ℝ (vecS c) x v = vecS (fun j n => c j n * lin n v) x := by
  rw [(hasFDerivAt_vecS hc x).fderiv]
  ext j
  change (fderiv ℝ (seriesC (c j)) x v).re = _
  rw [fderiv_seriesC_apply (hc j)]
  rfl

lemma fderiv_vecS {c : Fin 3 → Mode → ℂ} (hc : ∀ j, HS 1 (c j)) (v : T3) :
    (fun y => fderiv ℝ (vecS c) y v) = vecS (fun j n => c j n * lin n v) :=
  funext fun y => fderiv_vecS_apply hc y v

lemma lin_single_sq_sum (n : Mode) :
    ∑ i, lin n (EuclideanSpace.single i 1) * lin n (EuclideanSpace.single i 1) =
      -((4 * Real.pi ^ 2 * TorusFourierNS.ksq (TorusFourierNS.kvec n) : ℝ) : ℂ) := by
  simp only [lin_single, TorusFourierNS.ksq, TorusFourierNS.kvec]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (4 * (Real.pi : ℂ) ^ 2 * ((n i : ℝ) : ℂ) ^ 2) * this

/-- **Proved.** Laplacian of a vector series. -/
theorem laplacian_vecS {c : Fin 3 → Mode → ℂ} (hc : ∀ j, HS 3 (c j)) (x : T3) :
    laplacian (vecS c) x = vecS (fun j n =>
      -((4 * Real.pi ^ 2 * TorusFourierNS.ksq (TorusFourierNS.kvec n) : ℝ) : ℂ) * c j n) x := by
  unfold laplacian
  have h1 : ∀ j, HS 1 (c j) := fun j => (hc j).mono (by norm_num)
  have h2 : ∀ i j, HS 1 (fun n => c j n * lin n (EuclideanSpace.single i 1)) :=
    fun i j => ((hc j).mono (by norm_num : 2 ≤ 3)).mul_lin _
  simp only [fderiv_vecS h1]
  simp only [fderiv_vecS_apply (h2 _)]
  ext j
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [vecS_apply]
  rw [← Complex.re_sum, seriesC_sum3 fun i => ((h2 i j).mul_lin _).mono (Nat.zero_le _)]
  congr 2
  funext n
  rw [← lin_single_sq_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Proved.** Gradient of a scalar series. -/
theorem gradient_re_seriesC {q : Mode → ℂ} (hq : HS 1 q) (x : T3) (i : Fin 3) :
    pressureGradient (fun y => (seriesC q y).re) x i =
      (seriesC (fun n => 2 * Real.pi * Complex.I * ((n i : ℝ) : ℂ) * q n) x).re := by
  unfold pressureGradient
  rw [gradient_coord _ x i (hasFDerivAt_re_seriesC hq x).differentiableAt,
    fderiv_re_seriesC_apply hq]
  congr 2; funext n; rw [lin_single]; ring

/-! ### Cauchy product on `ℤ³` -/

lemma phase_add_sub (k m : Mode) (x : T3) : phase m x * phase (k - m) x = phase k x := by
  simp only [phase_eq]
  rw [← Complex.exp_add]
  congr 1
  simp only [lin_apply, Pi.sub_apply, Int.cast_sub, Complex.ofReal_sub, sub_mul,
    Finset.sum_sub_distrib]
  ring

lemma summable_fiber {A B : Mode → ℂ} (hB : Summable fun n => ‖B n‖)
    (hA : Summable fun n => ‖A n‖) (k : Mode) : Summable fun m => B m * A (k - m) := by
  have := ((summable_conv_nonneg hB hA (fun _ => norm_nonneg _) fun _ => norm_nonneg _).1).prod_factor k
  exact Summable.of_norm (this.congr fun m => (norm_mul _ _).symm)

lemma summable_conv_norm {A B : Mode → ℂ} (hB : Summable fun n => ‖B n‖)
    (hA : Summable fun n => ‖A n‖) : Summable fun k => ‖∑' m, B m * A (k - m)‖ := by
  refine ((summable_conv_nonneg hB hA (fun _ => norm_nonneg _) fun _ => norm_nonneg _).2.1).of_nonneg_of_le
    (fun _ => norm_nonneg _) fun k => ?_
  refine (norm_tsum_le_tsum_norm ?_).trans_eq (tsum_congr fun m => norm_mul _ _)
  exact (summable_fiber hB hA k).norm

lemma HS.conv {A B : Mode → ℂ} (hB : Summable fun n => ‖B n‖)
    (hA : Summable fun n => ‖A n‖) : HS 0 (fun k => ∑' m, B m * A (k - m)) :=
  (summable_conv_norm hB hA).congr fun k => by simp

/-- **Proved.** Cauchy product of two absolutely convergent Fourier series. -/
theorem seriesC_mul {A B : Mode → ℂ} (hB : Summable fun n => ‖B n‖)
    (hA : Summable fun n => ‖A n‖) (x : T3) :
    seriesC B x * seriesC A x = seriesC (fun k => ∑' m, B m * A (k - m)) x := by
  have nB : Summable fun n => ‖B n * phase n x‖ := hB.congr fun n => by rw [norm_mul, norm_phase, mul_one]
  have nA : Summable fun n => ‖A n * phase n x‖ := hA.congr fun n => by rw [norm_mul, norm_phase, mul_one]
  unfold seriesC
  rw [tsum_mul_tsum_of_summable_norm nB nA]
  let e : Mode × Mode ≃ Mode × Mode :=
    { toFun := fun p => (p.2, p.1 - p.2), invFun := fun q => (q.1 + q.2, q.1),
      left_inv := fun p => by simp, right_inv := fun q => by simp }
  have hp := summable_mul_of_summable_norm nB nA
  set F : Mode × Mode → ℂ := fun z => B z.1 * phase z.1 x * (A z.2 * phase z.2 x)
  have hq : Summable (F ∘ e) := (e.summable_iff (f := F)).2 hp
  rw [← e.tsum_eq F]
  refine hq.tsum_prod.trans ?_
  refine tsum_congr fun k => ?_
  rw [← tsum_mul_right]
  refine tsum_congr fun m => ?_
  simp only [F, e, Function.comp_apply, Equiv.coe_fn_mk]
  rw [← phase_add_sub k m x]
  ring


lemma summable_norm_int_mul {b : Mode → ℂ} (hb : HS 1 b) (l : Fin 3) :
    Summable fun n : Mode => ‖((n l : ℝ) : ℂ) * b n‖ :=
  hb.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, pow_one, mul_comm]
    exact mul_le_mul_of_nonneg_left (abs_int_le_bse n l) (norm_nonneg _)

/-- **Proved.** Convective term of the series velocity of a Hermitian field. -/
theorem seriesC_convective {b : FField} (hH : TorusFourierNS.HermitianField b)
    (hb : ∀ j, HS 1 (fun n => b n j)) (x : T3) (j : Fin 3) :
    seriesC (fun n => b n j * lin n (vecS (fun l n => b n l) x)) x =
      seriesC (fun k => nonlinCoeff b k j) x := by
  set S : Fin 3 → ℂ := fun l => seriesC (fun m => b m l) x with hS
  have hre : ∀ l, (((vecS (fun l n => b n l) x) l : ℝ) : ℂ) = S l := fun l => by
    rw [vecS_apply]
    exact Complex.conj_eq_iff_re.1 (conj_seriesC_of_hermitian (fun k => hH k l) x)
  set A : Fin 3 → Mode → ℂ := fun l n => ((n l : ℝ) : ℂ) * b n j with hA
  set B : Fin 3 → Mode → ℂ := fun l m => b m l with hB
  have nA : ∀ l, Summable fun n => ‖A l n‖ := fun l => summable_norm_int_mul (hb j) l
  have nB : ∀ l, Summable fun n => ‖B l n‖ := fun l => (hb l).summable_norm
  have hA0 : ∀ l, HS 0 (A l) := fun l => (nA l).congr fun n => by simp
  -- left side
  have hL : (fun n => b n j * lin n (vecS (fun l n => b n l) x)) =
      fun n => ∑ l, (2 * Real.pi * Complex.I * S l) * A l n := by
    funext n
    rw [lin_apply]
    simp only [hA, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [← hre l]; ring
  rw [hL, ← seriesC_sum3 fun l => (hA0 l).const_mul _]
  simp only [seriesC_const_mul]
  have hconv : ∀ l, S l * seriesC (A l) x = seriesC (fun k => ∑' m, B l m * A l (k - m)) x :=
    fun l => seriesC_mul (nB l) (nA l) x
  simp only [mul_assoc, hconv]
  simp only [← mul_assoc]
  -- right side
  have hR : (fun k => nonlinCoeff b k j) =
      fun k => ∑ l, (2 * Real.pi * Complex.I) * ∑' m, B l m * A l (k - m) := by
    funext k
    unfold nonlinCoeff convTerm
    rw [← Finset.mul_sum]
    congr 1
    have hs : ∀ l, Summable fun m => B l m * A l (k - m) := fun l => summable_fiber (nB l) (nA l) k
    rw [Fin.sum_univ_three, ← (hs 0).tsum_add (hs 1), ← ((hs 0).add (hs 1)).tsum_add (hs 2)]
    refine tsum_congr fun m => ?_
    simp only [hA, hB, Fin.sum_univ_three, Pi.sub_apply]
    push_cast
    ring
  rw [hR, ← seriesC_sum3 fun l => (HS.conv (nB l) (nA l)).const_mul _]
  simp only [seriesC_const_mul]

end PeriodicNSContinuation
