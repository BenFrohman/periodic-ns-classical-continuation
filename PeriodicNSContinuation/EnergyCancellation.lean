/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.EnergyEquality
import PeriodicNSContinuation.FourierData

/-!
# The nonlinear energy cancellation `⟨(u·∇)u, u⟩ = 0` on `𝕋³` (Fourier form)

**Proved here:** `periodicNonlinearEnergyCancellation : PeriodicNonlinearEnergyCancellation`.
Classical source: Leray (1934); Temam, *Navier–Stokes Equations* (1977), Ch. II, Lemma 1.3.

Proof (Fourier side). For smooth divergence-free periodic `v` with coefficients `a = v̂`:
* `a` is Hermitian (`a_{-k} = conj a_k`, real field) and divergence-free (`k·a_k = 0`);
* `a` decays faster than any power (`v ∈ H^s` for every `s`);
* the Leray projector drops out against `a_k` (`leray_pairing`);
* after the reindexing `(k, m) ↦ (m, k − m)` the double series is absolutely summable and the
  involution `(m, j) ↦ (m, −(m + j))` maps each term to its negative (Hermitian symmetry plus
  `m·a_m = 0`), so the sum vanishes.

Coined names: `jb`, `cfac`, `triT`, `preP`, `convG`. Nothing here concerns `PeriodicBKMIntegrability`
or Clay (B).
-/

noncomputable section
open Set Filter Topology FeffermanClayNS NavierStokes3D TorusFourierNS

namespace PeriodicNSContinuation

/-- Coined. `jb k = 1 + |k|²`. -/
def jb (k : Mode) : ℝ := 1 + nsq k

lemma one_le_jb (k : Mode) : 1 ≤ jb k := by unfold jb; linarith [nsq_nonneg k]
lemma jb_pos (k : Mode) : 0 < jb k := lt_of_lt_of_le one_pos (one_le_jb k)

lemma abs_mode_le_jb (k : Mode) (l : Fin 3) : |((k l : ℤ) : ℝ)| ≤ jb k := by
  have h1 : ((k l : ℤ) : ℝ) ^ 2 ≤ nsq k := by
    unfold nsq
    exact Finset.single_le_sum (f := fun i => ((k i : ℤ) : ℝ) ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ l)
  have h2 : |((k l : ℤ) : ℝ)| ≤ 1 + ((k l : ℤ) : ℝ) ^ 2 := by
    rw [← sq_abs]; nlinarith [sq_nonneg (|((k l : ℤ) : ℝ)| - 1)]
  unfold jb; linarith

lemma sobW_eq_jb_rpow (s : ℝ) (k : Mode) : sobW s k = jb k ^ s := rfl

lemma summable_jb_inv_sq : Summable fun k : Mode => (jb k ^ 2)⁻¹ := by
  refine (summable_sobW_neg (s := 2) (by norm_num)).congr fun k => ?_
  rw [sobW_eq_jb_rpow, Real.rpow_neg (jb_pos k).le]; norm_cast

lemma inv_pow_le_inv_sq (k : Mode) {n : ℕ} (hn : 2 ≤ n) : (jb k ^ n)⁻¹ ≤ (jb k ^ 2)⁻¹ :=
  inv_anti₀ (by have := jb_pos k; positivity) (pow_le_pow_right₀ (one_le_jb k) hn)

/-- Coefficient decay from `H⁸` membership. -/
lemma coeff_decay {a : FField} (ha : MemHsField 8 a) (k : Mode) (i : Fin 3) :
    ‖a k i‖ ≤ hsNormField 8 a * (jb k ^ 4)⁻¹ := by
  have h := coeff_le_hsNorm ha k i
  have hs : Real.sqrt (sobW 8 k) = jb k ^ 4 := by
    rw [sobW_eq_jb_rpow, show (8:ℝ) = ((8:ℕ):ℝ) by norm_num, Real.rpow_natCast,
      show jb k ^ 8 = (jb k ^ 4) ^ 2 by ring, Real.sqrt_sq (by have := jb_pos k; positivity)]
  rw [hs] at h
  have hp : 0 < jb k ^ 4 := by have := jb_pos k; positivity
  rw [le_mul_inv_iff₀ hp]; linarith

/-! ### The trilinear sum, abstractly -/

section Abstract

variable {a : FField} {H : ℝ}

/-- Coined. `cfac m j = a_m · j`. -/
def cfac (a : FField) (m j : Mode) : ℂ := ∑ l, a m l * (((j l : ℤ) : ℂ))

/-- Coined. `triT (m, j) = (a_m · j) ∑ᵢ conj(a_{m+j,i}) a_{j,i}`. -/
def triT (a : FField) (p : Mode × Mode) : ℂ :=
  cfac a p.1 p.2 * ∑ i, (starRingEnd ℂ) (a (p.1 + p.2) i) * a p.2 i

lemma norm_cfac_le (hB : ∀ k i, ‖a k i‖ ≤ H * (jb k ^ 4)⁻¹) (m j : Mode) :
    ‖cfac a m j‖ ≤ 3 * (H * (jb m ^ 4)⁻¹) * jb j := by
  unfold cfac
  refine (norm_sum_le _ _).trans ?_
  have : ∀ l ∈ (Finset.univ : Finset (Fin 3)), ‖a m l * (((j l : ℤ) : ℂ))‖ ≤ H * (jb m ^ 4)⁻¹ * jb j := by
    intro l _
    rw [norm_mul, Complex.norm_intCast]
    exact mul_le_mul (hB m l) (abs_mode_le_jb j l) (abs_nonneg _)
      ((norm_nonneg _).trans (hB m l))
  refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
  simp; ring

lemma H_nonneg (hB : ∀ k i, ‖a k i‖ ≤ H * (jb k ^ 4)⁻¹) : 0 ≤ H := by
  have h := (norm_nonneg _).trans (hB 0 0)
  have hp : 0 < (jb 0 ^ 4)⁻¹ := by have := jb_pos 0; positivity
  exact nonneg_of_mul_nonneg_left h hp

lemma norm_le_H (hB : ∀ k i, ‖a k i‖ ≤ H * (jb k ^ 4)⁻¹) (k : Mode) (i : Fin 3) : ‖a k i‖ ≤ H := by
  have h1 : (jb k ^ 4)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (one_le_jb k))
  have := H_nonneg hB
  exact (hB k i).trans (by nlinarith)

lemma jb_mul_inv_four (j : Mode) : jb j * (jb j ^ 4)⁻¹ ≤ (jb j ^ 2)⁻¹ := by
  have hp := jb_pos j
  rw [show jb j * (jb j ^ 4)⁻¹ = (jb j ^ 3)⁻¹ by field_simp]
  exact inv_pow_le_inv_sq j (by norm_num)

lemma norm_triT_le (hB : ∀ k i, ‖a k i‖ ≤ H * (jb k ^ 4)⁻¹) (p : Mode × Mode) :
    ‖triT a p‖ ≤ 9 * H ^ 3 * ((jb p.1 ^ 2)⁻¹ * (jb p.2 ^ 2)⁻¹) := by
  have hH := H_nonneg hB
  have hS : ‖∑ i, (starRingEnd ℂ) (a (p.1 + p.2) i) * a p.2 i‖ ≤ 3 * (H * (H * (jb p.2 ^ 4)⁻¹)) := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
        ‖(starRingEnd ℂ) (a (p.1 + p.2) i) * a p.2 i‖ ≤ H * (H * (jb p.2 ^ 4)⁻¹) := by
      intro i _
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (norm_le_H hB _ i) (hB _ i) (norm_nonneg _) hH
    refine (Finset.sum_le_sum this).trans (le_of_eq ?_); simp
  unfold triT
  rw [norm_mul]
  have hc := norm_cfac_le hB p.1 p.2
  have e1 := inv_pow_le_inv_sq p.1 (n := 4) (by norm_num)
  have e2 := jb_mul_inv_four p.2
  have hi1 : 0 ≤ (jb p.1 ^ 4)⁻¹ := by have := jb_pos p.1; positivity
  have hi2 : 0 ≤ (jb p.2 ^ 4)⁻¹ := by have := jb_pos p.2; positivity
  have hj2 : 0 ≤ (jb p.2 ^ 2)⁻¹ := by have := jb_pos p.2; positivity
  calc ‖cfac a p.1 p.2‖ * ‖∑ i, (starRingEnd ℂ) (a (p.1 + p.2) i) * a p.2 i‖
      ≤ (3 * (H * (jb p.1 ^ 4)⁻¹) * jb p.2) * (3 * (H * (H * (jb p.2 ^ 4)⁻¹))) :=
        mul_le_mul hc hS (norm_nonneg _) (by have := jb_pos p.2; positivity)
    _ = 9 * H ^ 3 * ((jb p.1 ^ 4)⁻¹ * (jb p.2 * (jb p.2 ^ 4)⁻¹)) := by ring
    _ ≤ 9 * H ^ 3 * ((jb p.1 ^ 2)⁻¹ * (jb p.2 ^ 2)⁻¹) := by
        gcongr
        · exact mul_nonneg (by have := jb_pos p.2; positivity) hi2

lemma summable_triT (hB : ∀ k i, ‖a k i‖ ≤ H * (jb k ^ 4)⁻¹) : Summable (triT a) := by
  refine Summable.of_norm_bounded ?_ (norm_triT_le hB)
  refine Summable.mul_left _ ?_
  exact summable_jb_inv_sq.mul_of_nonneg summable_jb_inv_sq
    (fun k => by have := jb_pos k; positivity) (fun k => by have := jb_pos k; positivity)

/-- The involution `(m, j) ↦ (m, −(m + j))`. -/
def triInv : Mode × Mode → Mode × Mode := fun p => (p.1, -(p.1 + p.2))

lemma triInv_involutive : Function.Involutive triInv := by
  intro p; simp only [triInv]; ext <;> simp

lemma triT_pair (hH : HermitianField a) (hD : DivergenceFree a) (p : Mode × Mode) :
    triT a p + triT a (triInv p) = 0 := by
  obtain ⟨m, j⟩ := p
  simp only [triT, triInv, cfac]
  have e1 : m + -(m + j) = -j := by abel
  rw [e1]
  have hc1 : ∀ i, (starRingEnd ℂ) (a (-j) i) = a j i := by
    intro i; rw [hH j i]; simp
  have hc2 : ∀ i, a (-(m + j)) i = (starRingEnd ℂ) (a (m + j) i) := fun i => hH (m + j) i
  simp only [hc1, hc2]
  have hdiv : (∑ l, a m l * ((j l : ℤ) : ℂ)) + ∑ l, a m l * (((-(m + j)) l : ℤ) : ℂ) = 0 := by
    have := hD m
    simp only [dot, kvec] at this
    rw [← Finset.sum_add_distrib]
    rw [← neg_eq_zero, ← this, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Pi.neg_apply, Pi.add_apply]; push_cast; ring
  have hs : ∑ i, a j i * (starRingEnd ℂ) (a (m + j) i) =
      ∑ i, (starRingEnd ℂ) (a (m + j) i) * a j i :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hs]
  linear_combination (∑ i, (starRingEnd ℂ) (a (m + j) i) * a j i) * hdiv

lemma tsum_triT_eq_zero (hH : HermitianField a) (hD : DivergenceFree a)
    (hB : ∀ k i, ‖a k i‖ ≤ H * (jb k ^ 4)⁻¹) : ∑' p, triT a p = 0 := by
  set σ := triInv_involutive.toPerm triInv
  have hs := summable_triT hB
  have hsσ : Summable (fun p => triT a (σ p)) := (σ.summable_iff).2 hs
  have h1 : ∑' p, triT a (σ p) = ∑' p, triT a p := σ.tsum_eq (triT a)
  have h2 : ∑' p, triT a p + ∑' p, triT a (σ p) = 0 := by
    rw [← hs.tsum_add hsσ]
    exact (tsum_congr fun p => triT_pair hH hD p).trans tsum_zero
  rw [h1] at h2
  linear_combination h2 / 2

/-- Coined. `preP (k, m) = (a_m · (k−m)) ∑ᵢ conj(a_{k,i}) a_{k−m,i}`. -/
def preP (a : FField) (p : Mode × Mode) : ℂ :=
  cfac a p.2 (p.1 - p.2) * ∑ i, (starRingEnd ℂ) (a p.1 i) * a (p.1 - p.2) i

/-- `(k, m) ↦ (m, k − m)`. -/
def kmEquiv : Mode × Mode ≃ Mode × Mode where
  toFun p := (p.2, p.1 - p.2)
  invFun q := (q.1 + q.2, q.1)
  left_inv p := by ext <;> simp
  right_inv q := by ext <;> simp

lemma preP_eq (p : Mode × Mode) : preP a p = triT a (kmEquiv p) := by
  simp [preP, triT, kmEquiv]

lemma summable_preP (hB : ∀ k i, ‖a k i‖ ≤ H * (jb k ^ 4)⁻¹) : Summable (preP a) := by
  have : preP a = triT a ∘ kmEquiv := funext fun p => preP_eq p
  rw [this]; exact (kmEquiv.summable_iff).2 (summable_triT hB)

lemma tsum_preP_eq_zero (hH : HermitianField a) (hD : DivergenceFree a)
    (hB : ∀ k i, ‖a k i‖ ≤ H * (jb k ^ 4)⁻¹) : ∑' p, preP a p = 0 := by
  have : preP a = triT a ∘ kmEquiv := funext fun p => preP_eq p
  rw [this]; exact (kmEquiv.tsum_eq (triT a)).trans (tsum_triT_eq_zero hH hD hB)

/-! ### The Fourier nonlinearity -/

/-- Coined. Convolution vector inside `fourierNSField`. -/
def convG (a : FField) (k : Mode) : Fin 3 → ℂ := fun j =>
  2 * Real.pi * Complex.I * ∑' m : Mode, (∑ l, a m l * ((((k - m) l : ℤ)) : ℂ)) * a (k - m) j

lemma nlField_eq (a : FField) (k : Mode) (i : Fin 3) :
    nlField a k i = -lerayP k (convG a k) i := by
  show -((viscCoeff 0 k : ℝ) : ℂ) * a k i - lerayP k (convG a k) i = _
  simp [viscCoeff]

lemma norm_conv_term_le (hB : ∀ k i, ‖a k i‖ ≤ H * (jb k ^ 4)⁻¹) (k m : Mode) (j : Fin 3) :
    ‖(∑ l, a m l * ((((k - m) l : ℤ)) : ℂ)) * a (k - m) j‖ ≤ 3 * H ^ 2 * (jb m ^ 2)⁻¹ := by
  have hH := H_nonneg hB
  rw [norm_mul]
  have hc := norm_cfac_le hB m (k - m)
  have e1 := inv_pow_le_inv_sq m (n := 4) (by norm_num)
  have e2 := jb_mul_inv_four (k - m)
  have h4 : 0 ≤ (jb m ^ 4)⁻¹ := by have := jb_pos m; positivity
  have h4' : 0 ≤ (jb (k - m) ^ 4)⁻¹ := by have := jb_pos (k - m); positivity
  calc ‖cfac a m (k - m)‖ * ‖a (k - m) j‖
      ≤ (3 * (H * (jb m ^ 4)⁻¹) * jb (k - m)) * (H * (jb (k - m) ^ 4)⁻¹) :=
        mul_le_mul hc (hB _ j) (norm_nonneg _) (by have := jb_pos (k - m); positivity)
    _ = 3 * H ^ 2 * ((jb m ^ 4)⁻¹ * (jb (k - m) * (jb (k - m) ^ 4)⁻¹)) := by ring
    _ ≤ 3 * H ^ 2 * ((jb m ^ 2)⁻¹ * 1) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul e1
          (e2.trans (inv_le_one_of_one_le₀ (one_le_pow₀ (one_le_jb _))))
          (mul_nonneg (jb_pos _).le h4') (by have := jb_pos m; positivity)) (by positivity)
    _ = 3 * H ^ 2 * (jb m ^ 2)⁻¹ := by ring

lemma summable_conv_term (hB : ∀ k i, ‖a k i‖ ≤ H * (jb k ^ 4)⁻¹) (k : Mode) (j : Fin 3) :
    Summable fun m : Mode => (∑ l, a m l * ((((k - m) l : ℤ)) : ℂ)) * a (k - m) j :=
  Summable.of_norm_bounded (summable_jb_inv_sq.mul_left _) fun m => norm_conv_term_le hB k m j

lemma norm_convG_le (hB : ∀ k i, ‖a k i‖ ≤ H * (jb k ^ 4)⁻¹) (k : Mode) (j : Fin 3) :
    ‖convG a k j‖ ≤ 2 * Real.pi * (3 * H ^ 2 * ∑' m : Mode, (jb m ^ 2)⁻¹) := by
  unfold convG
  rw [norm_mul]
  have h2 : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    simp [Real.pi_pos.le]
  rw [h2]
  gcongr
  refine (norm_tsum_le_tsum_norm (Summable.of_norm_bounded (summable_jb_inv_sq.mul_left _)
    fun m => (norm_norm _).le.trans (norm_conv_term_le hB k m j))).trans ?_
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun m => norm_conv_term_le hB k m j)
    (Summable.of_norm_bounded (summable_jb_inv_sq.mul_left _)
      fun m => (norm_norm _).le.trans (norm_conv_term_le hB k m j))
    (summable_jb_inv_sq.mul_left _)

/-- **Proved.** Componentwise bound for the Leray projector: `|(P_k w)_i| ≤ 2 ∑ⱼ |w_j|`. -/
lemma norm_lerayP_le_two (k : Mode) (w : Fin 3 → ℂ) (i : Fin 3) :
    ‖lerayP k w i‖ ≤ 2 * ∑ j, ‖w j‖ := by
  have hwi : ‖w i‖ ≤ ∑ j, ‖w j‖ :=
    Finset.single_le_sum (f := fun j => ‖w j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  have hsum0 : 0 ≤ ∑ j, ‖w j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  unfold lerayP
  by_cases hk : ksq (kvec k) = 0
  · simp [hk]; linarith
  have hkpos : 0 < ksq (kvec k) := lt_of_le_of_ne (by unfold ksq; positivity) (Ne.symm hk)
  have hsq : ∀ j, kvec k j ^ 2 ≤ ksq (kvec k) := fun j => by
    unfold ksq
    exact Finset.single_le_sum (f := fun j => kvec k j ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ j)
  have hpair : ∀ j, |kvec k j| * |kvec k i| ≤ ksq (kvec k) := fun j => by
    have := hsq j; have := hsq i
    nlinarith [sq_nonneg (|kvec k j| - |kvec k i|), sq_abs (kvec k j), sq_abs (kvec k i)]
  have hdot : ‖dot (kvec k) w‖ ≤ ∑ j, |kvec k j| * ‖w j‖ := by
    unfold dot
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hsec : ‖dot (kvec k) w / (ksq (kvec k) : ℂ) * (kvec k i : ℂ)‖ ≤ ∑ j, ‖w j‖ := by
    rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hkpos, div_mul_eq_mul_div, div_le_iff₀ hkpos]
    calc ‖dot (kvec k) w‖ * |kvec k i| ≤ (∑ j, |kvec k j| * ‖w j‖) * |kvec k i| :=
          mul_le_mul_of_nonneg_right hdot (abs_nonneg _)
      _ = ∑ j, (|kvec k j| * |kvec k i|) * ‖w j‖ := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ ∑ j, ksq (kvec k) * ‖w j‖ :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hpair j) (norm_nonneg _)
      _ = (∑ j, ‖w j‖) * ksq (kvec k) := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  calc ‖w i - dot (kvec k) w / (ksq (kvec k) : ℂ) * (kvec k i : ℂ)‖
      ≤ ‖w i‖ + ‖dot (kvec k) w / (ksq (kvec k) : ℂ) * (kvec k i : ℂ)‖ := norm_sub_le _ _
    _ ≤ 2 * ∑ j, ‖w j‖ := by linarith

/-- Per-mode identity: the transport pairing at `k` is `−2πi ∑ₘ preP(k, m)`. -/
lemma pairing_eq (hD : DivergenceFree a) (hB : ∀ k i, ‖a k i‖ ≤ H * (jb k ^ 4)⁻¹) (k : Mode) :
    ∑ i, (starRingEnd ℂ) (a k i) * nlField a k i =
      -(2 * Real.pi * Complex.I) * ∑' m, preP a (k, m) := by
  have e0 : ∑ i, (starRingEnd ℂ) (a k i) * nlField a k i =
      -∑ i, lerayP k (convG a k) i * (starRingEnd ℂ) (a k i) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [nlField_eq]; ring
  rw [e0, leray_pairing k (a k) (convG a k) (hD k)]
  have hsm : ∀ i ∈ (Finset.univ : Finset (Fin 3)), Summable fun m : Mode =>
      (∑ l, a m l * ((((k - m) l : ℤ)) : ℂ)) * a (k - m) i * (starRingEnd ℂ) (a k i) :=
    fun i _ => (summable_conv_term hB k i).mul_right _
  have e1 : ∀ i, convG a k i * (starRingEnd ℂ) (a k i) = 2 * Real.pi * Complex.I *
      ∑' m : Mode, (∑ l, a m l * ((((k - m) l : ℤ)) : ℂ)) * a (k - m) i * (starRingEnd ℂ) (a k i) := by
    intro i; unfold convG; rw [tsum_mul_right]; ring
  simp only [e1]
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum hsm]
  have e2 : ∀ m : Mode, ∑ i, (∑ l, a m l * ((((k - m) l : ℤ)) : ℂ)) * a (k - m) i *
      (starRingEnd ℂ) (a k i) = preP a (k, m) := by
    intro m; simp only [preP, cfac]; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [e2]; ring

/-- **Proved.** Abstract cancellation for a Hermitian, divergence-free, rapidly decaying field. -/
theorem nl_cancellation_abstract (hH : HermitianField a) (hD : DivergenceFree a)
    (hB : ∀ k i, ‖a k i‖ ≤ H * (jb k ^ 4)⁻¹) :
    Summable (fun p : Mode × Fin 3 => sobW 0 p.1 *
        (2 * ((starRingEnd ℂ) (a p.1 p.2) * nlField a p.1 p.2).re)) ∧
      rateOf 0 (nlField a) a = 0 := by
  have hH0 := H_nonneg hB
  set C : ℝ := 2 * (3 * (2 * Real.pi * (3 * H ^ 2 * ∑' m : Mode, (jb m ^ 2)⁻¹)))
  have hnl : ∀ k i, ‖nlField a k i‖ ≤ C := by
    intro k i
    rw [nlField_eq, norm_neg]
    refine (norm_lerayP_le_two k _ i).trans ?_
    have : ∑ j, ‖convG a k j‖ ≤ ∑ _j : Fin 3, 2 * Real.pi * (3 * H ^ 2 * ∑' m : Mode, (jb m ^ 2)⁻¹) :=
      Finset.sum_le_sum fun j _ => norm_convG_le hB k j
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    simp only [C]; push_cast at this; linarith
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hnl 0 0)
  have hsum : Summable (fun p : Mode × Fin 3 => sobW 0 p.1 *
      (2 * ((starRingEnd ℂ) (a p.1 p.2) * nlField a p.1 p.2).re)) := by
    refine Summable.of_norm_bounded (g := fun p : Mode × Fin 3 => 2 * C * H * (jb p.1 ^ 2)⁻¹)
      (summable_prod_fin3 (c := fun k => 2 * C * H * (jb k ^ 2)⁻¹)
        (fun k => by have := jb_pos k; positivity) (summable_jb_inv_sq.mul_left _)) ?_
    intro p
    rw [sobW_zero_eq, one_mul, Real.norm_eq_abs, abs_mul, abs_two]
    have h1 := Complex.abs_re_le_norm ((starRingEnd ℂ) (a p.1 p.2) * nlField a p.1 p.2)
    rw [norm_mul, Complex.norm_conj] at h1
    have h2 : ‖a p.1 p.2‖ * ‖nlField a p.1 p.2‖ ≤ (H * (jb p.1 ^ 4)⁻¹) * C :=
      mul_le_mul (hB _ _) (hnl _ _) (norm_nonneg _) (mul_nonneg hH0 (by have := jb_pos p.1; positivity))
    have h3 := inv_pow_le_inv_sq p.1 (n := 4) (by norm_num)
    have h4 : H * (jb p.1 ^ 4)⁻¹ * C ≤ H * (jb p.1 ^ 2)⁻¹ * C := by gcongr
    nlinarith
  refine ⟨hsum, ?_⟩
  have hP := summable_preP (a := a) hB
  unfold rateOf
  rw [hsum.tsum_prod]
  have e1 : ∀ k : Mode, ∑' i : Fin 3, sobW 0 (k, i).1 *
      (2 * ((starRingEnd ℂ) (a (k, i).1 (k, i).2) * nlField a (k, i).1 (k, i).2).re) =
      (-(4 * Real.pi * Complex.I) * ∑' m, preP a (k, m)).re := by
    intro k
    rw [tsum_fintype]
    simp only [sobW_zero_eq, one_mul]
    rw [← Finset.mul_sum, ← Complex.re_sum, pairing_eq hD hB k]
    rw [show -(4 * Real.pi * Complex.I) * ∑' m, preP a (k, m) =
      (2:ℂ) * (-(2 * Real.pi * Complex.I) * ∑' m, preP a (k, m)) by ring]
    generalize -(2 * Real.pi * Complex.I) * ∑' m, preP a (k, m) = w
    simp
  rw [tsum_congr e1, ← Complex.re_tsum ((hP.prod).mul_left _), tsum_mul_left,
    ← hP.tsum_prod, tsum_preP_eq_zero hH hD hB]
  simp

end Abstract

/-- **Proved.** `⟨(u·∇)u, u⟩ = 0` in Fourier form for smooth divergence-free periodic fields
(Leray 1934; Temam 1977, Ch. II, Lemma 1.3). Discharges `PeriodicNonlinearEnergyCancellation`. -/
theorem periodicNonlinearEnergyCancellation : PeriodicNonlinearEnergyCancellation := by
  intro v hv
  have hm := periodicDataHs 8 v hv
  exact nl_cancellation_abstract (fourierCoeffVF_hermitian v) (periodicDataDivFree v hv)
    (coeff_decay hm)

/-- **Proved (unconditional).** Time integrability of the enstrophy on a finite maximal interval:
`PeriodicEnstrophyTimeIntegrable ν` now holds with no hypothesis. -/
theorem periodicEnstrophyTimeIntegrable (ν : ℝ) : PeriodicEnstrophyTimeIntegrable ν :=
  periodicEnstrophyTimeIntegrable_of_cancellation periodicNonlinearEnergyCancellation ν

/-- **Proved (conditional).** `PeriodicBKMIntegrability` with the energy cancellation discharged;
the remaining inputs are the classical OPEN Props and the OPEN hidden property. -/
theorem periodicBKMIntegrability_of_classical_bending_std' {ν : ℝ}
    (hS : PeriodicHolderStretchingEstimate ν) (h2 : PeriodicH2SmoothingRateStd ν)
    (hI : PeriodicH2RootTimeIntegrable ν) (h3 : PeriodicH3SmoothingRate ν)
    (hB : PeriodicBendingRateHiddenProperty ν) : PeriodicBKMIntegrability ν :=
  periodicBKMIntegrability_of_classical_bending_std hS periodicNonlinearEnergyCancellation h2 hI h3 hB

end PeriodicNSContinuation
