/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.CellParseval

/-!
# Weighted Cauchy–Schwarz on the unit cell; shifts of trigonometric polynomials
(step 2 toward `PeriodicLowFreqVorticityBound`). All names coined (see README).
-/

noncomputable section
open Set MeasureTheory FeffermanClayNS NavierStokes3D TorusFourierNS

namespace PeriodicNSContinuation

lemma memLp_two_cell {f : (Fin 3 → ℝ) → ℝ} (hf : Continuous f) :
    MemLp f (ENNReal.ofReal 2) (volume.restrict (Icc (0 : Fin 3 → ℝ) 1)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.image_of_continuousOn hf.continuousOn).isBounded.exists_norm_le
  haveI : IsFiniteMeasure (volume.restrict (Icc (0 : Fin 3 → ℝ) 1)) :=
    isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  exact Filter.Eventually.of_forall fun x hx => hC _ ⟨x, hx, rfl⟩

/-- **Proved.** Cauchy–Schwarz on the cell for continuous nonnegative functions. -/
lemma cell_cauchySchwarz {f g : (Fin 3 → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    ∫ x in Icc (0 : Fin 3 → ℝ) 1, f x * g x ≤
      Real.sqrt (∫ x in Icc (0 : Fin 3 → ℝ) 1, f x ^ 2) *
        Real.sqrt (∫ x in Icc (0 : Fin 3 → ℝ) 1, g x ^ 2) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (Icc (0 : Fin 3 → ℝ) 1))
    (p := 2) (q := 2) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0)
    (memLp_two_cell hf) (memLp_two_cell hg)
  simpa only [Real.sqrt_eq_rpow, Real.rpow_two, one_div] using h

/-- **Proved.** Weighted Cauchy–Schwarz: for a continuous weight `W ≥ 1` and continuous `K`,
`∫ ‖K‖ ≤ √(∫ W⁻²) · √(∫ ‖W K‖²)`. -/
theorem cell_weighted_L1 {W : (Fin 3 → ℝ) → ℝ} {K : (Fin 3 → ℝ) → ℂ} (hW : Continuous W)
    (hW1 : ∀ x, 1 ≤ W x) (hK : Continuous K) :
    ∫ x in Icc (0 : Fin 3 → ℝ) 1, ‖K x‖ ≤
      Real.sqrt (∫ x in Icc (0 : Fin 3 → ℝ) 1, (W x)⁻¹ ^ 2) *
        Real.sqrt (∫ x in Icc (0 : Fin 3 → ℝ) 1, ‖(W x : ℂ) * K x‖ ^ 2) := by
  have hWpos : ∀ x, 0 < W x := fun x => by linarith [hW1 x]
  have e : ∀ x, ‖K x‖ = (W x)⁻¹ * ‖(W x : ℂ) * K x‖ := fun x => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hWpos x).le, ← mul_assoc,
      inv_mul_cancel₀ (hWpos x).ne', one_mul]
  simp_rw [e]
  exact cell_cauchySchwarz (hW.inv₀ fun x => (hWpos x).ne')
    ((Complex.continuous_ofReal.comp hW).mul hK).norm (fun x => (inv_pos.2 (hWpos x)).le)
    fun x => norm_nonneg _

/-- **Proved.** Multiplying a trigonometric polynomial by a character shifts its coefficients. -/
lemma charE_mul_multKernel (n : Mode) (S : Finset Mode) (c : Mode → ℂ) (z : Fin 3 → ℝ) :
    charE n z * multKernel S c z =
      multKernel (S.image (· + n)) (fun k => c (k - n)) z := by
  rw [multKernel, multKernel, Finset.mul_sum,
    Finset.sum_image fun a _ b _ h => add_right_cancel h]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : charE n z * charE k z = charE (k + n) z := by
    simp only [charE, ← Complex.exp_add]; congr 1
    simp only [Pi.add_apply, Int.cast_add, Complex.ofReal_add, add_mul, Finset.sum_add_distrib]
    ring
  rw [add_sub_cancel_right, ← this]; ring

/-- Coined. The box `{k : |k_i| ≤ N}` of modes. -/
def modeBox (N : ℕ) : Finset Mode := Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N

lemma mem_modeBox {N : ℕ} {k : Mode} : k ∈ modeBox N ↔ ∀ i, |k i| ≤ N := by
  simp [modeBox, abs_le]

lemma card_modeBox (N : ℕ) : (modeBox N).card = (2 * N + 1) ^ 3 := by
  simp only [modeBox, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  congr 1; omega

/-- Coined. `c` vanishes outside `modeBox N`. -/
def BoxSupp (N : ℕ) (c : Mode → ℂ) : Prop := ∀ k, k ∉ modeBox N → c k = 0

lemma multKernel_mono {N M : ℕ} (hNM : N ≤ M) {c : Mode → ℂ} (hc : BoxSupp N c)
    (z : Fin 3 → ℝ) : multKernel (modeBox N) c z = multKernel (modeBox M) c z := by
  refine Finset.sum_subset (fun k hk => mem_modeBox.2 fun i =>
    (mem_modeBox.1 hk i).trans (by exact_mod_cast hNM)) fun k _ hk => ?_
  rw [hc k hk, zero_mul]

/-- Coined. Unit shift vectors `±e_l`. -/
def unitMode (l : Fin 3) : Mode := Pi.single l 1

lemma boxSupp_shift {N : ℕ} {c : Mode → ℂ} (hc : BoxSupp N c) (n : Mode)
    (hn : ∀ i, |n i| ≤ 1) : BoxSupp (N + 1) fun k => c (k - n) := by
  intro k hk
  refine hc _ fun h => hk (mem_modeBox.2 fun i => ?_)
  have h1 := mem_modeBox.1 h i
  have h2 := hn i
  simp only [Pi.sub_apply] at h1
  push_cast
  calc |k i| = |(k i - n i) + n i| := by ring_nf
    _ ≤ |k i - n i| + |n i| := abs_add_le _ _
    _ ≤ N + 1 := by linarith

lemma charE_mul_multKernel_box {N : ℕ} {c : Mode → ℂ} (hc : BoxSupp N c) (n : Mode)
    (hn : ∀ i, |n i| ≤ 1) (z : Fin 3 → ℝ) :
    charE n z * multKernel (modeBox N) c z =
      multKernel (modeBox (N + 1)) (fun k => c (k - n)) z := by
  rw [charE_mul_multKernel]
  refine Finset.sum_subset (fun k hk => ?_) fun k _ hk => ?_
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hk
    refine mem_modeBox.2 fun i => ?_
    have := mem_modeBox.1 ha i; have := hn i
    simp only [Pi.add_apply]; push_cast
    exact (abs_add_le _ _).trans (by linarith)
  · have : k - n ∉ modeBox N := fun h => hk (Finset.mem_image.2 ⟨k - n, h, by simp⟩)
    simp only [hc _ this, zero_mul]

lemma abs_unitMode (l : Fin 3) (i : Fin 3) : |unitMode l i| ≤ 1 ∧ |(-unitMode l) i| ≤ 1 := by
  by_cases h : i = l
  · subst h; simp [unitMode]
  · simp [unitMode, h]

lemma multKernel_add (S : Finset Mode) (c d : Mode → ℂ) (z : Fin 3 → ℝ) :
    multKernel S (fun k => c k + d k) z = multKernel S c z + multKernel S d z := by
  simp only [multKernel, add_mul, Finset.sum_add_distrib]

lemma multKernel_smul (S : Finset Mode) (a : ℂ) (c : Mode → ℂ) (z : Fin 3 → ℝ) :
    multKernel S (fun k => a * c k) z = a * multKernel S c z := by
  simp only [multKernel, Finset.mul_sum, mul_assoc]

lemma normSq_charE_sub_one (l : Fin 3) (z : Fin 3 → ℝ) :
    ((‖charE (unitMode l) z - 1‖ ^ 2 : ℝ) : ℂ) =
      2 - charE (unitMode l) z - charE (-unitMode l) z := by
  have hc : charE (-unitMode l) z = (starRingEnd ℂ) (charE (unitMode l) z) := by
    have := charE_mul_conj 0 (unitMode l) z
    simp only [zero_sub] at this
    rw [← this]; simp [charE]
  have hn : charE (unitMode l) z * (starRingEnd ℂ) (charE (unitMode l) z) = 1 := by
    rw [charE_mul_conj, sub_self]; simp [charE]
  rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sub, map_one, hc]
  linear_combination hn

/-- Coined. Discrete Laplacian-type sum of centred second differences
`Σ_l (c(k+e_l) − 2c(k) + c(k−e_l))`. -/
def secDiffSum (c : Mode → ℂ) (k : Mode) : ℂ :=
  ∑ l, (c (k + unitMode l) - 2 * c k + c (k - unitMode l))

/-- Coined. Weight `W_A(z) = 1 + A Σ_l |e(z_l) − 1|²`. -/
def cellWeight (A : ℝ) (z : Fin 3 → ℝ) : ℝ := 1 + A * ∑ l, ‖charE (unitMode l) z - 1‖ ^ 2

lemma continuous_cellWeight (A : ℝ) : Continuous (cellWeight A) :=
  continuous_const.add (continuous_const.mul (continuous_finset_sum _ fun l _ =>
    ((continuous_charE _).sub continuous_const).norm.pow 2))

lemma one_le_cellWeight {A : ℝ} (hA : 0 ≤ A) (z : Fin 3 → ℝ) : 1 ≤ cellWeight A z :=
  le_add_of_nonneg_right (mul_nonneg hA (Finset.sum_nonneg fun l _ => sq_nonneg _))

/-- **Proved.** `W_A · K_c` is the trigonometric polynomial with coefficients `c − A Σ_l Δ_l² c`. -/
theorem cellWeight_mul_multKernel {N : ℕ} {c : Mode → ℂ} (hc : BoxSupp N c) (A : ℝ)
    (z : Fin 3 → ℝ) :
    (cellWeight A z : ℂ) * multKernel (modeBox N) c z =
      multKernel (modeBox (N + 1)) (fun k => c k - A * secDiffSum c k) z := by
  have hp : ∀ l, charE (unitMode l) z * multKernel (modeBox N) c z =
      multKernel (modeBox (N + 1)) (fun k => c (k - unitMode l)) z := fun l =>
    charE_mul_multKernel_box hc _ (fun i => (abs_unitMode l i).1) z
  have hm : ∀ l, charE (-unitMode l) z * multKernel (modeBox N) c z =
      multKernel (modeBox (N + 1)) (fun k => c (k + unitMode l)) z := fun l => by
    rw [charE_mul_multKernel_box hc _ (fun i => (abs_unitMode l i).2) z]
    simp only [sub_neg_eq_add]
  have h0 := multKernel_mono (Nat.le_succ N) hc z
  have hr : multKernel (modeBox (N + 1)) (fun k => c k - A * secDiffSum c k) z =
      multKernel (modeBox (N + 1)) c z - A * ∑ l,
        (multKernel (modeBox (N + 1)) (fun k => c (k + unitMode l)) z -
          2 * multKernel (modeBox (N + 1)) c z +
          multKernel (modeBox (N + 1)) (fun k => c (k - unitMode l)) z) := by
    simp only [multKernel, secDiffSum, Fin.sum_univ_three, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [hr, ← h0]
  simp only [cellWeight, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul,
    normSq_charE_sub_one, Fin.sum_univ_three] at hp hm ⊢
  rw [← hp 0, ← hp 1, ← hp 2, ← hm 0, ← hm 1, ← hm 2]
  ring

lemma norm_charE (k : Mode) (x : Fin 3 → ℝ) : ‖charE k x‖ = 1 := by
  rw [charE, Complex.norm_exp]
  simp [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.mul_im]

lemma multKernel_sub_eq_conj (T : Finset Mode) (d : Mode → ℂ) (x y : Fin 3 → ℝ) :
    multKernel T d (x - y) =
      (starRingEnd ℂ) (multKernel T (fun k => (starRingEnd ℂ) (d k * charE k x)) y) := by
  rw [multKernel, multKernel, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e2 : charE k (x - y) = charE k x * (starRingEnd ℂ) (charE k y) := by
    have := charE_mul_conj k k y
    have h3 : charE k (x - y) * charE k y = charE k x := by
      simp only [charE, ← Complex.exp_add]; congr 1
      simp only [Pi.sub_apply, Complex.ofReal_sub, mul_sub, Finset.sum_sub_distrib]; ring
    rw [← h3, mul_assoc, this, sub_self]; simp [charE]
  rw [e2, map_mul, map_mul, map_mul, Complex.conj_conj, Complex.conj_conj]; ring

/-- **Proved.** Translated Parseval: `∫_y |K_d(x − y)|² = Σ |d_k|²`. -/
theorem integral_normSq_multKernel_sub (T : Finset Mode) (d : Mode → ℂ) (x : Fin 3 → ℝ) :
    ∫ y in Icc (0 : Fin 3 → ℝ) 1, ‖multKernel T d (x - y)‖ ^ 2 = ∑ k ∈ T, ‖d k‖ ^ 2 := by
  simp_rw [multKernel_sub_eq_conj, Complex.norm_conj]
  rw [integral_normSq_multKernel]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.norm_conj, norm_mul, norm_charE, mul_one]

end PeriodicNSContinuation
