/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.GalerkinLimit

/-!
# `GalerkinModeEquiLipschitz` and `GalerkinLimitEquation` for `s > 2`

**Proved:** `galerkinModeEquiLipschitz (hs : 2 < s)` and `galerkinLimitEquation (hs : 2 < s)`.
The key estimate is a pointwise bound on the convolution term,
`‖convTerm a k m j‖ ≤ convConst s M k · (1+|m|²)^{-(s-1/2)}`, which is summable in `m`
exactly when `s > 2` (Peetre's inequality). This gives a uniform-in-`N` bound on every mode of
the vector field, hence the Lipschitz bound, and Tannery's theorem plus dominated convergence pass
to the limit in the integrated equation. All names are coined.
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D

namespace PeriodicNSContinuation

/-- Base `1 + |k|²` (coined). -/
def bse (k : TorusFourierNS.Mode) : ℝ := 1 + ∑ i, ((k i : ℝ)) ^ 2

lemma one_le_bse (k : TorusFourierNS.Mode) : 1 ≤ bse k := by
  unfold bse; linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => sq_nonneg ((k i : ℝ))]

lemma bse_pos (k : TorusFourierNS.Mode) : 0 < bse k := lt_of_lt_of_le one_pos (one_le_bse k)

lemma sobW_eq (s : ℝ) (k : TorusFourierNS.Mode) : TorusFourierNS.sobW s k = bse k ^ s := rfl

/-- Convolution term of the Fourier nonlinearity (coined). -/
def convTerm (a : TorusFourierNS.FField) (k m : TorusFourierNS.Mode) (j : Fin 3) : ℂ :=
  (∑ l, a m l * ((((k - m) l : ℤ)) : ℂ)) * a (k - m) j

/-- Pointwise decay `‖a m l‖ ≤ M (1+|m|²)^{-s/2}` (coined). -/
def PtBound (s M : ℝ) (a : TorusFourierNS.FField) : Prop :=
  ∀ m l, ‖a m l‖ ≤ M * bse m ^ (-(s / 2))

lemma ptBound_of_hs {s M : ℝ} {N : ℕ} {v : TorusFourierNS.GState N}
    (hv : TorusFourierNS.hsNormField s (TorusFourierNS.extendG v) ≤ M) :
    PtBound s M (TorusFourierNS.extendG v) := fun m l => by
  have hM : 0 ≤ M := (Real.sqrt_nonneg _).trans hv
  refine (norm_extendG_le_of_hs hv m l).trans (le_of_eq ?_)
  have hb := bse_pos m
  rw [sobW_eq, Real.sqrt_div (sq_nonneg M), Real.sqrt_sq hM, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hb.le, Real.rpow_neg hb.le, div_eq_mul_inv]
  congr 3; ring

lemma ptBound_of_tendsto {s M : ℝ} {x : ℕ → TorusFourierNS.FField} {a : TorusFourierNS.FField}
    (hx : ∀ n, PtBound s M (x n)) (h : ∀ k i, Tendsto (fun n => x n k i) atTop (𝓝 (a k i))) :
    PtBound s M a := fun m l => le_of_tendsto' (h m l).norm fun n => hx n m l

/-- **Proved.** Peetre-type inequality `1+|m|² ≤ 2 (1+|k|²)(1+|k-m|²)`. -/
lemma bse_le (k m : TorusFourierNS.Mode) : bse m ≤ 2 * bse k * bse (k - m) := by
  unfold bse
  have h1 : ∑ i, ((m i : ℝ)) ^ 2 ≤ 2 * ∑ i, ((k i : ℝ)) ^ 2 + 2 * ∑ i, (((k - m) i : ℤ) : ℝ) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    push_cast [Pi.sub_apply]
    nlinarith [sq_nonneg ((k i : ℝ) + ((k i : ℝ) - m i))]
  have hX := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => sq_nonneg ((k i : ℝ))
  have hY := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => sq_nonneg ((((k - m) i : ℤ) : ℝ))
  nlinarith [mul_nonneg hX hY]

lemma abs_le_bse_half (n : TorusFourierNS.Mode) (l : Fin 3) : |((n l : ℤ) : ℝ)| ≤ bse n ^ (1 / 2 : ℝ) := by
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  unfold bse
  have := Finset.single_le_sum (f := fun i => ((n i : ℝ)) ^ 2) (fun i _ => sq_nonneg _)
    (Finset.mem_univ l)
  linarith

/-- Constant of the convolution bound (coined). -/
def convConst (s M : ℝ) (k : TorusFourierNS.Mode) : ℝ := 3 * M ^ 2 * (2 * bse k) ^ ((s - 1) / 2)

lemma convConst_nonneg (s M : ℝ) (k : TorusFourierNS.Mode) : 0 ≤ convConst s M k := by
  unfold convConst
  have := bse_pos k
  positivity

/-- **Proved.** Pointwise bound on the convolution term. -/
theorem norm_convTerm_le {s M : ℝ} (hs : 1 ≤ s) (hM : 0 ≤ M) {a : TorusFourierNS.FField}
    (ha : PtBound s M a) (k m : TorusFourierNS.Mode) (j : Fin 3) :
    ‖convTerm a k m j‖ ≤ convConst s M k * bse m ^ (-(s - 1 / 2)) := by
  set t := (s - 1) / 2 with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  have hbm := bse_pos m
  have hbk := bse_pos k
  have hbd := bse_pos (k - m)
  have hS : ‖∑ l, a m l * ((((k - m) l : ℤ)) : ℂ)‖ ≤
      3 * (M * bse m ^ (-(s / 2)) * bse (k - m) ^ (1 / 2 : ℝ)) := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ l ∈ Finset.univ, ‖a m l * ((((k - m) l : ℤ)) : ℂ)‖ ≤
        M * bse m ^ (-(s / 2)) * bse (k - m) ^ (1 / 2 : ℝ) := fun l _ => by
      rw [norm_mul, Complex.norm_intCast]
      exact mul_le_mul (ha m l) (abs_le_bse_half _ l) (abs_nonneg _) (by positivity)
    refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
    simp
  have hD : bse (k - m) ^ (-t) ≤ (2 * bse k) ^ t * bse m ^ (-t) := by
    rw [Real.rpow_neg hbd.le, Real.rpow_neg hbm.le, ← div_eq_mul_inv,
      le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity), ← Real.mul_rpow hbd.le
      (by positivity)]
    exact Real.rpow_le_rpow hbm.le (by linarith [bse_le k m]) ht0
  have e1 : bse (k - m) ^ (1 / 2 : ℝ) * bse (k - m) ^ (-(s / 2)) = bse (k - m) ^ (-t) := by
    rw [← Real.rpow_add hbd]; congr 1; rw [ht]; ring
  have e2 : bse m ^ (-(s / 2)) * bse m ^ (-t) = bse m ^ (-(s - 1 / 2)) := by
    rw [← Real.rpow_add hbm]; congr 1; rw [ht]; ring
  unfold convTerm
  rw [norm_mul]
  calc ‖∑ l, a m l * ((((k - m) l : ℤ)) : ℂ)‖ * ‖a (k - m) j‖
      ≤ 3 * (M * bse m ^ (-(s / 2)) * bse (k - m) ^ (1 / 2 : ℝ)) *
          (M * bse (k - m) ^ (-(s / 2))) := mul_le_mul hS (ha _ j) (norm_nonneg _) (by positivity)
    _ = 3 * M ^ 2 * bse m ^ (-(s / 2)) *
          (bse (k - m) ^ (1 / 2 : ℝ) * bse (k - m) ^ (-(s / 2))) := by ring
    _ = 3 * M ^ 2 * bse m ^ (-(s / 2)) * bse (k - m) ^ (-t) := by rw [e1]
    _ ≤ 3 * M ^ 2 * bse m ^ (-(s / 2)) * ((2 * bse k) ^ t * bse m ^ (-t)) :=
        mul_le_mul_of_nonneg_left hD (by positivity)
    _ = convConst s M k * (bse m ^ (-(s / 2)) * bse m ^ (-t)) := by unfold convConst; ring
    _ = convConst s M k * bse m ^ (-(s - 1 / 2)) := by rw [e2]

lemma summable_bse {s : ℝ} (hs : 2 < s) : Summable fun m : TorusFourierNS.Mode => bse m ^ (-(s - 1 / 2)) :=
  TorusFourierNS.summable_sobW_neg (s := s - 1 / 2) (by linarith)

/-- `Σ_m (1+|m|²)^{-(s-1/2)}` (coined). -/
def bseSum (s : ℝ) : ℝ := ∑' m : TorusFourierNS.Mode, bse m ^ (-(s - 1 / 2))

lemma bseSum_nonneg (s : ℝ) : 0 ≤ bseSum s :=
  tsum_nonneg fun m => Real.rpow_nonneg (bse_pos m).le _

lemma summable_convTerm {s M : ℝ} (hs : 2 < s) (hM : 0 ≤ M) {a : TorusFourierNS.FField}
    (ha : PtBound s M a) (k : TorusFourierNS.Mode) (j : Fin 3) :
    Summable fun m => ‖convTerm a k m j‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun m => norm_convTerm_le (by linarith) hM ha k m j) ((summable_bse hs).mul_left _)

lemma norm_tsum_convTerm_le {s M : ℝ} (hs : 2 < s) (hM : 0 ≤ M) {a : TorusFourierNS.FField}
    (ha : PtBound s M a) (k : TorusFourierNS.Mode) (j : Fin 3) :
    ‖∑' m, convTerm a k m j‖ ≤ convConst s M k * bseSum s := by
  refine (norm_tsum_le_tsum_norm (summable_convTerm hs hM ha k j)).trans ?_
  rw [bseSum, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun m => norm_convTerm_le (by linarith) hM ha k m j)
    (summable_convTerm hs hM ha k j) ((summable_bse hs).mul_left _)

/-- **Proved.** The Leray projector is bounded componentwise. -/
lemma norm_lerayP_le (k : TorusFourierNS.Mode) (w : Fin 3 → ℂ) (i : Fin 3) :
    ‖TorusFourierNS.lerayP k w i‖ ≤ 2 * ∑ j, ‖w j‖ := by
  have hwi : ‖w i‖ ≤ ∑ j, ‖w j‖ :=
    Finset.single_le_sum (f := fun j => ‖w j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  have hsum0 : 0 ≤ ∑ j, ‖w j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  unfold TorusFourierNS.lerayP
  set q := TorusFourierNS.ksq (TorusFourierNS.kvec k)
  have hq0 : 0 ≤ q := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hkk : ∀ j, |TorusFourierNS.kvec k j| * |TorusFourierNS.kvec k i| ≤ q := fun j => by
    have hj := Finset.single_le_sum (f := fun l => TorusFourierNS.kvec k l ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    have hi := Finset.single_le_sum (f := fun l => TorusFourierNS.kvec k l ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    simp only at hj hi
    have hqd : q = ∑ x, TorusFourierNS.kvec k x ^ 2 := rfl
    rw [hqd]
    nlinarith [sq_nonneg (|TorusFourierNS.kvec k j| - |TorusFourierNS.kvec k i|), sq_abs
      (TorusFourierNS.kvec k j), sq_abs (TorusFourierNS.kvec k i)]
  have hdot : ‖TorusFourierNS.dot (TorusFourierNS.kvec k) w‖ * |TorusFourierNS.kvec k i| ≤
      q * ∑ j, ‖w j‖ := by
    unfold TorusFourierNS.dot
    calc _ ≤ (∑ j, |TorusFourierNS.kvec k j| * ‖w j‖) * |TorusFourierNS.kvec k i| := by
          refine mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans (le_of_eq ?_)) (abs_nonneg _)
          congr 1; funext j; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ = ∑ j, (|TorusFourierNS.kvec k j| * |TorusFourierNS.kvec k i|) * ‖w j‖ := by
          rw [Finset.sum_mul]; congr 1; funext j; ring
      _ ≤ ∑ j, q * ‖w j‖ := Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (hkk j) (norm_nonneg _)
      _ = q * ∑ j, ‖w j‖ := by rw [Finset.mul_sum]
  refine (norm_sub_le _ _).trans ?_
  by_cases hq : q = 0
  · simp [hq]; linarith
  · have hqp : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
    have : ‖TorusFourierNS.dot (TorusFourierNS.kvec k) w / (q : ℂ) *
        (TorusFourierNS.kvec k i : ℂ)‖ ≤ ∑ j, ‖w j‖ := by
      rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos hqp, div_mul_eq_mul_div, div_le_iff₀ hqp]
      linarith
    linarith

/-- Uniform mode bound for the vector field (coined). -/
def lipC (ν s M : ℝ) (k : TorusFourierNS.Mode) : ℝ :=
  |TorusFourierNS.viscCoeff ν k| * M + 2 * 3 * (2 * Real.pi * (convConst s M k * bseSum s))

lemma lipC_nonneg (ν s : ℝ) {M : ℝ} (hM : 0 ≤ M) (k : TorusFourierNS.Mode) : 0 ≤ lipC ν s M k := by
  unfold lipC
  have := convConst_nonneg s M k
  have := bseSum_nonneg s
  have := Real.pi_pos
  positivity

/-- **Proved.** Every mode of the full Fourier NS field is bounded on `PtBound` fields. -/
theorem norm_fourierNSField_le {ν s M : ℝ} (hs : 2 < s) (hM : 0 ≤ M) {a : TorusFourierNS.FField}
    (ha : PtBound s M a) (k : TorusFourierNS.Mode) (i : Fin 3) :
    ‖fourierNSField ν a k i‖ ≤ lipC ν s M k := by
  have hak : ‖a k i‖ ≤ M := (ha k i).trans (mul_le_of_le_one_right hM
    (Real.rpow_le_one_of_one_le_of_nonpos (one_le_bse k) (by linarith)))
  have hT : ∀ j, ‖2 * Real.pi * Complex.I * ∑' m, convTerm a k m j‖ ≤
      2 * Real.pi * (convConst s M k * bseSum s) := fun j => by
    rw [norm_mul]
    have h2 : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
      rw [norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]; norm_num
    rw [h2]
    exact mul_le_mul_of_nonneg_left (norm_tsum_convTerm_le hs hM ha k j) (by positivity)
  unfold fourierNSField lipC
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hak (abs_nonneg _)
  · refine (norm_lerayP_le k _ i).trans ?_
    have := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hT j
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    change 2 * ∑ j, ‖2 * Real.pi * Complex.I * ∑' m, convTerm a k m j‖ ≤ _
    push_cast at this
    linarith


/-- **Proved.** Inside the box, the Galerkin field is the full Fourier field of `extendG u`. -/
theorem galerkinNSField_eq (ν : ℝ) {N : ℕ} (u : TorusFourierNS.GState N) (k : TorusFourierNS.Mode)
    (hk : k ∈ TorusFourierNS.modeBox N) (i : Fin 3) :
    TorusFourierNS.galerkinNSField N ν u ⟨k, hk⟩ i = fourierNSField ν (TorusFourierNS.extendG u) k i := by
  rw [TorusFourierNS.galerkinNSField_apply]
  have hg : TorusFourierNS.gconv u u k = fun j => 2 * Real.pi * Complex.I * ∑' m : TorusFourierNS.Mode,
      (∑ l, TorusFourierNS.extendG u m l * ((((k - m) l : ℤ)) : ℂ)) * TorusFourierNS.extendG u (k - m) j := by
    funext j
    unfold TorusFourierNS.gconv
    congr 1
    rw [tsum_eq_sum (f := fun m : TorusFourierNS.Mode =>
      (∑ l, TorusFourierNS.extendG u m l * ((((k - m) l : ℤ)) : ℂ)) * TorusFourierNS.extendG u (k - m) j)
      (s := TorusFourierNS.modeBox N) (fun m hm => by
      simp [TorusFourierNS.extendG, hm])]
    symm
    rw [← Finset.sum_coe_sort]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [TorusFourierNS.extendG_apply]
  have hu : TorusFourierNS.extendG u k = u ⟨k, hk⟩ := TorusFourierNS.extendG_apply u ⟨k, hk⟩
  unfold fourierNSField
  change _ = _ - TorusFourierNS.lerayP k _ i
  rw [← hg, hu, Complex.real_smul, sub_eq_add_neg]
  push_cast
  rfl

/-- **Proved.** Componentwise derivative and continuity of a Galerkin solution. -/
lemma galerkin_component {ν T : ℝ} {N : ℕ} {a₀ : TorusFourierNS.FField} {α : ℝ → TorusFourierNS.GState N}
    (hα : IsGalerkinSolutionOn N ν a₀ T α) (k : TorusFourierNS.Mode) (hk : k ∈ TorusFourierNS.modeBox N)
    (i : Fin 3) :
    (∀ τ ∈ Icc 0 T, HasDerivAt (fun τ => α τ ⟨k, hk⟩ i)
      (fourierNSField ν (TorusFourierNS.extendG (α τ)) k i) τ) ∧
    ContinuousOn (fun τ => fourierNSField ν (TorusFourierNS.extendG (α τ)) k i) (Icc 0 T) := by
  have hd : ∀ τ ∈ Icc 0 T, HasDerivAt (fun τ => α τ ⟨k, hk⟩ i)
      (fourierNSField ν (TorusFourierNS.extendG (α τ)) k i) τ := fun τ hτ => by
    have := hasDerivAt_pi.1 (hasDerivAt_pi.1 (hα.2 τ hτ) ⟨k, hk⟩) i
    rwa [galerkinNSField_eq] at this
  refine ⟨hd, ?_⟩
  refine ContinuousOn.congr (f := fun τ => TorusFourierNS.galerkinNSField N ν (α τ) ⟨k, hk⟩ i) ?_
    (fun τ _ => (galerkinNSField_eq ν _ k hk i).symm)
  intro τ hτ
  have hc : ContinuousAt α τ := (hα.2 τ hτ).continuousAt
  have hF := (TorusFourierNS.galerkinNSField_contDiff (N := N) ν).continuous
  exact (((continuous_apply i).comp ((continuous_apply (⟨k, hk⟩ : TorusFourierNS.modeBox N)).comp
    hF)).continuousAt.comp hc).continuousWithinAt

/-- **Proved for `s > 2`** (the hypothesis is needed for the summable convolution bound). -/
theorem galerkinModeEquiLipschitz {ν s : ℝ} (hs : 2 < s) : GalerkinModeEquiLipschitz ν s := by
  intro u₀ _ T hT M α hαs hαb
  have hM : 0 ≤ M := (Real.sqrt_nonneg _).trans (hαb 0 0 ⟨le_rfl, hT.le⟩)
  refine ⟨fun k => lipC ν s M k, fun N t₁ h₁ t₂ h₂ k i => ?_⟩
  by_cases hk : k ∈ TorusFourierNS.modeBox N
  · obtain ⟨hd, -⟩ := galerkin_component (hαs N) k hk i
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hd t ht).hasDerivWithinAt)
      (fun t ht => norm_fourierNSField_le hs hM (ptBound_of_hs (hαb N t ht)) k i)
      (convex_Icc 0 T) h₂ h₁
    simpa [TorusFourierNS.extendG, hk, Real.norm_eq_abs] using this
  · simp only [TorusFourierNS.extendG, hk, dite_false, sub_self, norm_zero]
    exact mul_nonneg (lipC_nonneg ν s hM k) (abs_nonneg _)

/-- **Proved.** Modewise convergence of `PtBound` fields gives convergence of every mode of the
Fourier NS field (Tannery's theorem). -/
theorem tendsto_fourierNSField {ν s M : ℝ} (hs : 2 < s) (hM : 0 ≤ M)
    {x : ℕ → TorusFourierNS.FField} {a : TorusFourierNS.FField} (hx : ∀ n, PtBound s M (x n))
    (h : ∀ k i, Tendsto (fun n => x n k i) atTop (𝓝 (a k i))) (k : TorusFourierNS.Mode) (i : Fin 3) :
    Tendsto (fun n => fourierNSField ν (x n) k i) atTop (𝓝 (fourierNSField ν a k i)) := by
  have hT : ∀ j, Tendsto (fun n => ∑' m, convTerm (x n) k m j) atTop (𝓝 (∑' m, convTerm a k m j)) :=
    fun j => tendsto_tsum_of_dominated_convergence ((summable_bse hs).mul_left (convConst s M k))
      (fun m => ((tendsto_finset_sum _ fun l _ => (h m l).mul_const _).mul (h (k - m) j)))
      (Eventually.of_forall fun n m => norm_convTerm_le (by linarith) hM (hx n) k m j)
  have hw : ∀ j, Tendsto (fun n => 2 * Real.pi * Complex.I * ∑' m, convTerm (x n) k m j) atTop
      (𝓝 (2 * Real.pi * Complex.I * ∑' m, convTerm a k m j)) := fun j => (hT j).const_mul _
  have hL : Tendsto (fun n => TorusFourierNS.lerayP k
      (fun j => 2 * Real.pi * Complex.I * ∑' m, convTerm (x n) k m j) i) atTop
      (𝓝 (TorusFourierNS.lerayP k (fun j => 2 * Real.pi * Complex.I * ∑' m, convTerm a k m j) i)) := by
    unfold TorusFourierNS.lerayP TorusFourierNS.dot
    exact (hw i).sub (((tendsto_finset_sum _ fun j _ => (hw j).const_mul _).div_const _).mul_const _)
  exact ((h k i).const_mul _).sub hL

/-- **Proved for `s > 2`.** The limit satisfies the integrated Fourier NS equation. -/
theorem galerkinLimitEquation {ν s : ℝ} (hs : 2 < s) : GalerkinLimitEquation ν s := by
  intro u₀ _ T hT M α hαs hαb φ hφ a hconv t ht k i
  have hM : 0 ≤ M := (Real.sqrt_nonneg _).trans (hαb 0 0 ⟨le_rfl, hT.le⟩)
  have hev : ∀ᶠ n in atTop, k ∈ TorusFourierNS.modeBox (φ n) :=
    hφ.tendsto_atTop.eventually (eventually_mem_modeBox k)
  have hsub : uIcc 0 t ⊆ Icc 0 T := by
    rw [uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2
  have hIoc : uIoc 0 t ⊆ Icc 0 T := fun τ hτ => hsub (uIoc_subset_uIcc hτ)
  have hftc : ∀ n, k ∈ TorusFourierNS.modeBox (φ n) →
      TorusFourierNS.extendG (α (φ n) 0) k i +
        ∫ τ in (0 : ℝ)..t, fourierNSField ν (TorusFourierNS.extendG (α (φ n) τ)) k i =
      TorusFourierNS.extendG (α (φ n) t) k i := by
    intro n hk
    obtain ⟨hd, hc⟩ := galerkin_component (hαs (φ n)) k hk i
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ hτ => hd τ (hsub hτ))
      ((hc.mono hsub).intervalIntegrable)]
    simp [TorusFourierNS.extendG, hk]
  have hint : Tendsto (fun n => ∫ τ in (0 : ℝ)..t,
      fourierNSField ν (TorusFourierNS.extendG (α (φ n) τ)) k i) atTop
      (𝓝 (∫ τ in (0 : ℝ)..t, fourierNSField ν (a τ) k i)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => lipC ν s M k) ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [hev] with n hk
      exact ((galerkin_component (hαs (φ n)) k hk i).2.mono hIoc).aestronglyMeasurable
        measurableSet_uIoc
    · exact Eventually.of_forall fun n => ae_of_all _ fun τ hτ =>
        norm_fourierNSField_le hs hM (ptBound_of_hs (hαb _ τ (hIoc hτ))) k i
    · exact ae_of_all _ fun τ hτ => tendsto_fourierNSField hs hM
        (fun n => ptBound_of_hs (hαb _ τ (hIoc hτ))) (hconv τ (hIoc hτ)) k i
  exact tendsto_nhds_unique (hconv t ht k i)
    (((hconv 0 ⟨le_rfl, hT.le⟩ k i).add hint).congr' (by
      filter_upwards [hev] with n hk; exact hftc n hk))

/-- **Proved (conditional on `FourierSolutionReconstruction` only), for `s > 2`.** -/
theorem periodicGalerkinLimit_of_reconstruction {ν s : ℝ} (hs : 2 < s)
    (hD : FourierSolutionReconstruction ν s) : PeriodicGalerkinLimit ν s :=
  periodicGalerkinLimit_of' (galerkinModeEquiLipschitz hs) (galerkinLimitEquation hs) hD

end PeriodicNSContinuation
