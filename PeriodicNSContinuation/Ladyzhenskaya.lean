/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.LatticeSum
import PeriodicNSContinuation.MeanConservation

/-!
# A Ladyzhenskaya-type trilinear estimate on `T³` (discharging `PeriodicH1TrilinearBound`)

Credit: the interpolation inequalities used here are classical and due to
O. A. Ladyzhenskaya — the 2D inequality `‖u‖²_{L⁴} ≤ C‖u‖_{L²}‖∇u‖_{L²}` (1958) and its 3D
analogue `‖u‖⁴_{L⁴} ≤ C‖u‖_{L²}‖∇u‖³_{L²}`, published in her 1961 monograph *The
Mathematical Theory of Viscous Incompressible Flow* (Russian ed. 1961; English 1963).
Nothing here is new mathematics.

What is formalized is not literally the `L⁴` inequality but a Fourier-side estimate of
the same (subcritical, `H¹`–`H²`) type, proved via an Agmon-style `ℓ¹` interpolation
(`enn_agmon`, using the explicit lattice sum `latticeSum_le`), Young `ℓ¹ * ℓ² → ℓ²`,
Cauchy–Schwarz and an `ℓ¹` bound on the Leray projector. The constant `ladyK` is explicit
and far from optimal. This does **not** settle global regularity: the conditional
small-data theorem below still assumes `PeriodicH1BlowupCriterion`.
-/

noncomputable section
open Set Filter Topology Finset
open scoped ENNReal
open FeffermanClayNS NavierStokes3D

namespace PeriodicNSContinuation

lemma enn_mul_le_sq_add_sq (x y : ℝ≥0∞) : x * y ≤ x ^ 2 + y ^ 2 := by
  rcases le_total x y with h | h
  · calc x * y ≤ y * y := mul_le_mul_left h y
      _ ≤ _ := by rw [← sq]; exact le_add_self
  · calc x * y ≤ x * x := mul_le_mul_right h x
      _ ≤ _ := by rw [← sq]; exact le_self_add

lemma enn_tsum_mul_tsum {ι κ : Type*} (f : ι → ℝ≥0∞) (g : κ → ℝ≥0∞) :
    (∑' i, f i) * (∑' j, g j) = ∑' i, ∑' j, f i * g j := by
  rw [← ENNReal.tsum_mul_right]; congr 1; funext i; rw [ENNReal.tsum_mul_left]

/-- **Proved.** Cauchy–Schwarz in `ℝ≥0∞` (with a harmless factor 2). -/
lemma enn_cauchySchwarz {ι : Type*} (f g : ι → ℝ≥0∞) :
    (∑' i, f i * g i) ^ 2 ≤ 2 * ((∑' i, f i ^ 2) * (∑' i, g i ^ 2)) := by
  rw [sq, enn_tsum_mul_tsum]
  calc ∑' i, ∑' j, f i * g i * (f j * g j)
      ≤ ∑' i, ∑' j, (f i ^ 2 * g j ^ 2 + f j ^ 2 * g i ^ 2) := by
        refine ENNReal.tsum_le_tsum fun i => ENNReal.tsum_le_tsum fun j => ?_
        calc f i * g i * (f j * g j) = (f i * g j) * (f j * g i) := by ring
          _ ≤ (f i * g j) ^ 2 + (f j * g i) ^ 2 := enn_mul_le_sq_add_sq _ _
          _ = _ := by ring
    _ = 2 * ((∑' i, f i ^ 2) * (∑' i, g i ^ 2)) := by
        simp_rw [ENNReal.tsum_add]
        rw [ENNReal.tsum_comm (f := fun i j => f j ^ 2 * g i ^ 2), ← enn_tsum_mul_tsum,
          two_mul]

/-- **Proved.** Young's convolution inequality `ℓ¹ * ℓ² → ℓ²` on an additive group
(with a factor 2). -/
lemma enn_young {G : Type*} [AddCommGroup G] (f g : G → ℝ≥0∞) :
    ∑' k, (∑' m, f m * g (k - m)) ^ 2 ≤ 2 * ((∑' m, f m) ^ 2 * ∑' k, g k ^ 2) := by
  have hshift : ∀ m : G, ∑' k, g (k - m) ^ 2 = ∑' k, g k ^ 2 := fun m =>
    (Equiv.subRight m).tsum_eq (fun k => g k ^ 2)
  calc ∑' k, (∑' m, f m * g (k - m)) ^ 2
      ≤ ∑' k, ∑' m, ∑' n, (f m * f n * g (k - m) ^ 2 + f m * f n * g (k - n) ^ 2) := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        rw [sq, enn_tsum_mul_tsum]
        refine ENNReal.tsum_le_tsum fun m => ENNReal.tsum_le_tsum fun n => ?_
        calc f m * g (k - m) * (f n * g (k - n)) = (f m * f n) * (g (k - m) * g (k - n)) := by ring
          _ ≤ (f m * f n) * (g (k - m) ^ 2 + g (k - n) ^ 2) :=
              mul_le_mul_right (enn_mul_le_sq_add_sq _ _) _
          _ = _ := by ring
    _ = ∑' m, ∑' n, (f m * f n * ∑' k, g (k - m) ^ 2 + f m * f n * ∑' k, g (k - n) ^ 2) := by
        rw [ENNReal.tsum_comm]; congr 1; funext m
        rw [ENNReal.tsum_comm]; congr 1; funext n
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    _ = 2 * ((∑' m, f m) ^ 2 * ∑' k, g k ^ 2) := by
        simp_rw [hshift, ← add_mul, ← two_mul]
        have e : ∀ m n, 2 * f m * f n * ∑' k, g k ^ 2 = 2 * (∑' k, g k ^ 2) * (f m * f n) :=
          fun m n => by ring
        simp_rw [e, ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_mul_right, sq]; ring

/-- **Proved.** Optimizing `a ≤ c (μ e + x / μ)` over `μ > 0`. -/
lemma real_opt {a e x c : ℝ} (ha : 0 ≤ a) (he : 0 ≤ e) (hx : 0 ≤ x) (hc : 0 ≤ c)
    (h : ∀ μ : ℝ, 0 < μ → a ≤ c * (μ * e + x / μ)) : a ^ 2 ≤ 4 * c ^ 2 * x * e := by
  rcases he.lt_or_eq with he | he
  · rcases hx.lt_or_eq with hx | hx
    · have hsx := Real.sqrt_pos.mpr hx; have hse := Real.sqrt_pos.mpr he
      have h1 := h (Real.sqrt x / Real.sqrt e) (div_pos hsx hse)
      have ex := Real.sq_sqrt hx.le; have ee := Real.sq_sqrt he.le
      have : Real.sqrt x / Real.sqrt e * e + x / (Real.sqrt x / Real.sqrt e)
          = 2 * (Real.sqrt x * Real.sqrt e) := by
        field_simp; rw [ex, ee]; ring
      rw [this] at h1
      have h2 : a ^ 2 ≤ (c * (2 * (Real.sqrt x * Real.sqrt e))) ^ 2 :=
        pow_le_pow_left₀ ha h1 2
      calc a ^ 2 ≤ _ := h2
        _ = 4 * c ^ 2 * (Real.sqrt x) ^ 2 * (Real.sqrt e) ^ 2 := by ring
        _ = _ := by rw [ex, ee]
    · subst hx
      suffices a = 0 by subst this; simp
      by_contra hne
      have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hne)
      have h1 := h (a / (2 * (c * e + 1))) (by positivity)
      simp only [zero_div, add_zero] at h1
      have : c * (a / (2 * (c * e + 1)) * e) < a := by
        rw [show c * (a / (2 * (c * e + 1)) * e) = a * (c * e / (2 * (c * e + 1))) by ring]
        have : c * e / (2 * (c * e + 1)) < 1 := by
          rw [div_lt_one (by positivity)]; nlinarith [mul_nonneg hc he.le]
        nlinarith
      linarith
  · subst he
    suffices a = 0 by subst this; simp
    by_contra hne
    have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hne)
    have h1 := h (2 * (c * x + 1) / a) (by positivity)
    simp only [mul_zero, zero_add] at h1
    have : c * (x / (2 * (c * x + 1) / a)) < a := by
      rw [show c * (x / (2 * (c * x + 1) / a)) = a * (c * x / (2 * (c * x + 1))) by
        field_simp]
      have : c * x / (2 * (c * x + 1)) < 1 := by
        rw [div_lt_one (by positivity)]; nlinarith [mul_nonneg hc hx]
      nlinarith
    linarith

open TorusFourierNS in
/-- **Proved.** Weighted Cauchy–Schwarz plus `latticeSum_le`: the Fourier `ℓ¹` norm is
controlled by `μ ‖·‖²_{H¹} + μ⁻¹ ‖·‖²_{H²}` for every `μ > 0` (Agmon/Ladyzhenskaya-type). -/
lemma enn_agmon_mu {μ : ℝ} (hμ : 0 < μ) (α : Mode → ℝ≥0∞) :
    (∑' k, α k) ^ 2 ≤ 2 * (ENNReal.ofReal 12000 * (ENNReal.ofReal μ *
      (∑' k, ENNReal.ofReal (jsq k) * α k ^ 2) +
      (∑' k, ENNReal.ofReal (jsq k ^ 2) * α k ^ 2) / ENNReal.ofReal μ)) := by
  set w : Mode → ℝ := fun k => jsq k * (μ ^ 2 + jsq k) / μ
  have hs := one_le_jsq
  have hw0 : ∀ k, 0 ≤ w k := fun k => by have := hs k; positivity
  have hl0 : ∀ k, 0 ≤ latW μ (jsq k) := fun k => by have := hs k; unfold latW; positivity
  have hprod : ∀ k, Real.sqrt (latW μ (jsq k)) * Real.sqrt (w k) = 1 := fun k => by
    rw [← Real.sqrt_mul (hl0 k)]
    have := hs k
    have : latW μ (jsq k) * w k = 1 := by
      simp only [latW, w]; field_simp
    rw [this, Real.sqrt_one]
  have hfg : ∀ k, α k = ENNReal.ofReal (Real.sqrt (latW μ (jsq k))) *
      (ENNReal.ofReal (Real.sqrt (w k)) * α k) := fun k => by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), hprod, ENNReal.ofReal_one,
      one_mul]
  rw [tsum_congr hfg]
  refine (enn_cauchySchwarz _ _).trans ?_
  gcongr
  · calc ∑' k, ENNReal.ofReal (Real.sqrt (latW μ (jsq k))) ^ 2
          = ∑' k, ENNReal.ofReal (latW μ (jsq k)) := by
            congr 1; funext k
            rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (hl0 k)]
      _ ≤ _ := latticeSum_le hμ
  · apply le_of_eq
    have hk : ∀ k, (ENNReal.ofReal (Real.sqrt (w k)) * α k) ^ 2 =
        ENNReal.ofReal μ * (ENNReal.ofReal (jsq k) * α k ^ 2) +
          (ENNReal.ofReal (jsq k ^ 2) * α k ^ 2) * (ENNReal.ofReal μ)⁻¹ := fun k => by
      have := hs k
      rw [mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (hw0 k)]
      have : w k = μ * jsq k + jsq k ^ 2 / μ := by simp only [w]; field_simp
      rw [this, ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hμ.le,
        ENNReal.ofReal_div_of_pos hμ, div_eq_mul_inv]
      ring
    simp_rw [hk]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, div_eq_mul_inv]

open TorusFourierNS in
/-- **Proved.** Ladyzhenskaya/Agmon-type interpolation on `T³`, Fourier side:
`‖α‖_{ℓ¹}⁴ ≤ 4·24000² · (∑ ⟨k⟩⁴ α_k²) (∑ ⟨k⟩² α_k²)`. -/
theorem enn_agmon (α : Mode → ℝ≥0∞)
    (hE : (∑' k, ENNReal.ofReal (jsq k) * α k ^ 2) ≠ ⊤)
    (hX : (∑' k, ENNReal.ofReal (jsq k ^ 2) * α k ^ 2) ≠ ⊤) :
    ((∑' k, α k) ^ 2) ^ 2 ≤ ENNReal.ofReal (4 * 24000 ^ 2) *
      (∑' k, ENNReal.ofReal (jsq k ^ 2) * α k ^ 2) * (∑' k, ENNReal.ofReal (jsq k) * α k ^ 2) := by
  set E := ∑' k, ENNReal.ofReal (jsq k) * α k ^ 2
  set X := ∑' k, ENNReal.ofReal (jsq k ^ 2) * α k ^ 2
  set A := (∑' k, α k) ^ 2
  have hA : ∀ μ : ℝ, 0 < μ → A ≤ ENNReal.ofReal 24000 * (ENNReal.ofReal μ * E + X / ENNReal.ofReal μ) :=
    fun μ hμ => by
      refine (enn_agmon_mu hμ α).trans (le_of_eq ?_)
      rw [← mul_assoc, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]; norm_num; rfl
  have hAt : A ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (hA 1 one_pos)
    simp only [ENNReal.ofReal_one, one_mul, div_one]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr ⟨hE, hX⟩)
  have hr : ∀ μ : ℝ, 0 < μ → A.toReal ≤ 24000 * (μ * E.toReal + X.toReal / μ) := fun μ hμ => by
    have h := hA μ hμ
    have hne : ENNReal.ofReal 24000 * (ENNReal.ofReal μ * E + X / ENNReal.ofReal μ) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE,
          ENNReal.div_ne_top hX (by simpa using hμ)⟩)
    have := (ENNReal.toReal_le_toReal hAt hne).mpr h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE)
      (ENNReal.div_ne_top hX (by simpa using hμ)), ENNReal.toReal_mul, ENNReal.toReal_div,
      ENNReal.toReal_ofReal hμ.le, ENNReal.toReal_ofReal (by norm_num)] at this
  have key := real_opt ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    (by norm_num) hr
  rw [← ENNReal.ofReal_toReal hAt, ← ENNReal.ofReal_toReal hE, ← ENNReal.ofReal_toReal hX,
    ← ENNReal.ofReal_pow ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

open TorusFourierNS in
lemma abs_kvec_le_sqrt (k : Mode) (i : Fin 3) : |kvec k i| ≤ Real.sqrt (ksq (kvec k)) :=
  Real.abs_le_sqrt (Finset.single_le_sum (f := fun j => kvec k j ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ i))

open TorusFourierNS in
/-- **Proved.** The Fourier Leray projector is bounded on `ℓ¹(Fin 3)`, with constant 4. -/
lemma lerayP_l1_le (k : Mode) (w : Fin 3 → ℂ) :
    ∑ i, ‖lerayP k w i‖ ≤ 4 * ∑ j, ‖w j‖ := by
  have hdot : ‖dot (kvec k) w‖ ≤ ∑ j, |kvec k j| * ‖w j‖ := by
    unfold dot
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp [Complex.norm_real]
  have hK0 : 0 ≤ ksq (kvec k) := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hterm : ∀ i, ‖lerayP k w i‖ ≤ ‖w i‖ + ∑ j, ‖w j‖ := fun i => by
    unfold lerayP
    refine (norm_sub_le _ _).trans (add_le_add_right ?_ _)
    rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hK0]
    rcases hK0.lt_or_eq with hK | hK
    · rw [div_mul_eq_mul_div, div_le_iff₀ hK]
      calc ‖dot (kvec k) w‖ * |kvec k i|
          ≤ (∑ j, |kvec k j| * ‖w j‖) * |kvec k i| :=
            mul_le_mul_of_nonneg_right hdot (abs_nonneg _)
        _ = ∑ j, (|kvec k j| * |kvec k i|) * ‖w j‖ := by rw [Finset.sum_mul]; congr 1; funext j; ring
        _ ≤ ∑ j, ksq (kvec k) * ‖w j‖ := by
            refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            calc |kvec k j| * |kvec k i| ≤ Real.sqrt (ksq (kvec k)) * Real.sqrt (ksq (kvec k)) :=
                  mul_le_mul (abs_kvec_le_sqrt k j) (abs_kvec_le_sqrt k i) (abs_nonneg _)
                    (Real.sqrt_nonneg _)
              _ = ksq (kvec k) := Real.mul_self_sqrt hK0
        _ = (∑ j, ‖w j‖) * ksq (kvec k) := by rw [Finset.sum_mul]; congr 1; funext j; ring
    · rw [← hK]; simp; exact Finset.sum_nonneg fun j _ => norm_nonneg _
  calc ∑ i, ‖lerayP k w i‖ ≤ ∑ i, (‖w i‖ + ∑ j, ‖w j‖) := Finset.sum_le_sum fun i _ => hterm i
    _ = 4 * ∑ j, ‖w j‖ := by rw [Finset.sum_add_distrib]; simp; ring

open TorusFourierNS

/-- `ℓ¹(Fin 3)` size of the mode-`k` coefficient, in `ℝ≥0∞`. -/
def alph (a : FField) (k : Mode) : ℝ≥0∞ := ∑ i, ‖a k i‖ₑ

/-- `⟨k⟩ = (1 + |k|²)^{1/2}`, in `ℝ≥0∞`. -/
def rho (k : Mode) : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt (jsq k))

lemma enorm_int_le_rho (n : Mode) (l : Fin 3) : ‖(((n l : ℤ)) : ℂ)‖ₑ ≤ rho n := by
  rw [← ofReal_norm_eq_enorm, Complex.norm_intCast]
  refine ENNReal.ofReal_le_ofReal (Real.abs_le_sqrt ?_)
  unfold jsq
  have := Finset.single_le_sum (f := fun j => ((n j : ℤ) : ℝ) ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ l)
  simp only at this; linarith

/-- **Proved.** Pointwise bound on the nonlinear Fourier field:
`∑ᵢ |N(a)_k,i| ≤ 8π ∑_m α_m ⟨k-m⟩ α_{k-m}`. -/
lemma nlField_enorm_le (a : FField) (k : Mode) :
    ∑ i, ‖nlField a k i‖ₑ ≤
      ENNReal.ofReal (8 * Real.pi) * ∑' m, alph a m * (rho (k - m) * alph a (k - m)) := by
  set w : Fin 3 → ℂ := fun j => 2 * Real.pi * Complex.I * ∑' m : Mode,
      (∑ l, a m l * ((((k - m) l : ℤ)) : ℂ)) * a (k - m) j with hw
  have hnl : ∀ i, nlField a k i = -(lerayP k w i) := fun i => by
    simp [nlField, fourierNSField, viscCoeff, w]
  have h1 : ∑ i, ‖nlField a k i‖ₑ ≤ 4 * ∑ j, ‖w j‖ₑ := by
    simp_rw [hnl, enorm_neg, ← ofReal_norm_eq_enorm]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _),
      ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _), ← ENNReal.ofReal_ofNat 4,
      ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (lerayP_l1_le k w)
  have hc : ∀ m, ‖∑ l, a m l * ((((k - m) l : ℤ)) : ℂ)‖ₑ ≤ alph a m * rho (k - m) := fun m => by
    refine (enorm_sum_le _ _).trans ?_
    unfold alph; rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun l _ => by
      rw [enorm_mul]; exact mul_le_mul_right (enorm_int_le_rho _ _) _
  have h2 : ∀ j, ‖w j‖ₑ ≤ ENNReal.ofReal (2 * Real.pi) *
      ∑' m, alph a m * rho (k - m) * ‖a (k - m) j‖ₑ := fun j => by
    simp only [w]
    rw [enorm_mul]
    have e1 : ‖(2 : ℂ) * Real.pi * Complex.I‖ₑ = ENNReal.ofReal (2 * Real.pi) := by
      rw [← ofReal_norm_eq_enorm]; congr 1
      simp [abs_of_pos Real.pi_pos]
    rw [e1]
    refine mul_le_mul_right ((enorm_tsum_le_tsum_enorm).trans
      (ENNReal.tsum_le_tsum fun m => ?_)) _
    rw [enorm_mul]; exact mul_le_mul_left (hc m) _
  calc ∑ i, ‖nlField a k i‖ₑ ≤ 4 * ∑ j, ‖w j‖ₑ := h1
    _ ≤ 4 * ∑ j, ENNReal.ofReal (2 * Real.pi) * ∑' m, alph a m * rho (k - m) * ‖a (k - m) j‖ₑ :=
        mul_le_mul_right (Finset.sum_le_sum fun j _ => h2 j) _
    _ = 4 * ENNReal.ofReal (2 * Real.pi) * ∑' m, ∑ j, alph a m * rho (k - m) * ‖a (k - m) j‖ₑ := by
        rw [← Finset.mul_sum, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), mul_assoc]
    _ = ENNReal.ofReal (8 * Real.pi) * ∑' m, alph a m * (rho (k - m) * alph a (k - m)) := by
        rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        · ring_nf
        · congr 1; funext m; rw [← Finset.mul_sum]; unfold alph; ring

lemma rho_sq (k : Mode) : rho k ^ 2 = ENNReal.ofReal (jsq k) := by
  unfold rho
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (by linarith [one_le_jsq k])]

/-- **Proved.** The Fourier-side trilinear estimate in `ℝ≥0∞`: with
`E = ∑ ⟨k⟩² α_k²`, `X = ∑ ⟨k⟩⁴ α_k²` and `R = ∑ 2⟨k⟩² α_k ∑ᵢ|N(a)_k,i|`,
`R⁴ ≤ 256 (8π)⁴ · 4·24000² · X³ E³`. -/
theorem enn_trilinear (a : FField)
    (hE : (∑' k, ENNReal.ofReal (jsq k) * alph a k ^ 2) ≠ ⊤)
    (hX : (∑' k, ENNReal.ofReal (jsq k ^ 2) * alph a k ^ 2) ≠ ⊤) :
    (∑' k, 2 * ENNReal.ofReal (jsq k) * alph a k * ∑ i, ‖nlField a k i‖ₑ) ^ 4 ≤
      ENNReal.ofReal (256 * (8 * Real.pi) ^ 4 * (4 * 24000 ^ 2)) *
      (∑' k, ENNReal.ofReal (jsq k ^ 2) * alph a k ^ 2) ^ 3 *
      (∑' k, ENNReal.ofReal (jsq k) * alph a k ^ 2) ^ 3 := by
  set E := ∑' k, ENNReal.ofReal (jsq k) * alph a k ^ 2
  set X := ∑' k, ENNReal.ofReal (jsq k ^ 2) * alph a k ^ 2
  set nu : Mode → ℝ≥0∞ := fun k => ∑ i, ‖nlField a k i‖ₑ
  set S := ∑' k, alph a k
  have hc8 : ENNReal.ofReal (8 * Real.pi) ^ 2 = ENNReal.ofReal ((8 * Real.pi) ^ 2) :=
    (ENNReal.ofReal_pow (by positivity) 2).symm
  -- ∑ ν² ≤ 2 (8π)² S² E
  have hN : ∑' k, nu k ^ 2 ≤ 2 * ENNReal.ofReal ((8 * Real.pi) ^ 2) * (S ^ 2 * E) := by
    calc ∑' k, nu k ^ 2 ≤ ∑' k, (ENNReal.ofReal (8 * Real.pi) *
          ∑' m, alph a m * (rho (k - m) * alph a (k - m))) ^ 2 :=
          ENNReal.tsum_le_tsum fun k => pow_le_pow_left₀ (zero_le _) (nlField_enorm_le a k) 2
      _ = ENNReal.ofReal ((8 * Real.pi) ^ 2) *
          ∑' k, (∑' m, alph a m * (fun n => rho n * alph a n) (k - m)) ^ 2 := by
          rw [← hc8, ← ENNReal.tsum_mul_left]; congr 1; funext k; rw [mul_pow]
      _ ≤ ENNReal.ofReal ((8 * Real.pi) ^ 2) *
          (2 * (S ^ 2 * ∑' k, (rho k * alph a k) ^ 2)) := mul_le_mul_right (enn_young _ _) _
      _ = 2 * ENNReal.ofReal ((8 * Real.pi) ^ 2) * (S ^ 2 * E) := by
          simp_rw [mul_pow, rho_sq]; ring
  have hR2 : (∑' k, 2 * ENNReal.ofReal (jsq k) * alph a k * nu k) ^ 2 ≤
      8 * X * ∑' k, nu k ^ 2 := by
    have e : ∀ k, 2 * ENNReal.ofReal (jsq k) * alph a k * nu k =
        2 * ((ENNReal.ofReal (jsq k) * alph a k) * nu k) := fun k => by ring
    simp_rw [e]
    rw [ENNReal.tsum_mul_left, mul_pow]
    calc (2:ℝ≥0∞) ^ 2 * (∑' k, ENNReal.ofReal (jsq k) * alph a k * nu k) ^ 2
        ≤ 2 ^ 2 * (2 * ((∑' k, (ENNReal.ofReal (jsq k) * alph a k) ^ 2) * ∑' k, nu k ^ 2)) :=
          mul_le_mul_right (enn_cauchySchwarz _ _) _
      _ = 8 * X * ∑' k, nu k ^ 2 := by
          have : ∀ k, (ENNReal.ofReal (jsq k) * alph a k) ^ 2 = ENNReal.ofReal (jsq k ^ 2) * alph a k ^ 2 :=
            fun k => by rw [mul_pow, ENNReal.ofReal_pow (by linarith [one_le_jsq k])]
          simp_rw [this]; ring
  have hA := enn_agmon (alph a) hE hX
  calc (∑' k, 2 * ENNReal.ofReal (jsq k) * alph a k * nu k) ^ 4
      = ((∑' k, 2 * ENNReal.ofReal (jsq k) * alph a k * nu k) ^ 2) ^ 2 := by ring
    _ ≤ (8 * X * (2 * ENNReal.ofReal ((8 * Real.pi) ^ 2) * (S ^ 2 * E))) ^ 2 :=
        pow_le_pow_left₀ (zero_le _) (hR2.trans (mul_le_mul_right hN _)) 2
    _ = 256 * ENNReal.ofReal ((8 * Real.pi) ^ 2) ^ 2 * X ^ 2 * E ^ 2 * (S ^ 2) ^ 2 := by ring
    _ ≤ 256 * ENNReal.ofReal ((8 * Real.pi) ^ 2) ^ 2 * X ^ 2 * E ^ 2 *
        (ENNReal.ofReal (4 * 24000 ^ 2) * X * E) := mul_le_mul_right hA _
    _ = ENNReal.ofReal (256 * (8 * Real.pi) ^ 4 * (4 * 24000 ^ 2)) * X ^ 3 * E ^ 3 := by
        have hk : (256:ℝ≥0∞) * ENNReal.ofReal ((8 * Real.pi) ^ 2) ^ 2 * ENNReal.ofReal (4 * 24000 ^ 2)
            = ENNReal.ofReal (256 * (8 * Real.pi) ^ 4 * (4 * 24000 ^ 2)) := by
          rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_ofNat 256,
            ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
        rw [← hk]; ring

lemma sobW_one_jsq (k : Mode) : sobW 1 k = jsq k := by
  unfold sobW jsq; rw [Real.rpow_one]

lemma sobW_two_jsq (k : Mode) : sobW 2 k = jsq k ^ 2 := by
  unfold sobW jsq; rw [Real.rpow_two]

lemma alph_sq_le (a : FField) (k : Mode) : alph a k ^ 2 ≤ 6 * ∑ i, ‖a k i‖ₑ ^ 2 := by
  have h := enn_cauchySchwarz (fun _ : Fin 3 => (1 : ℝ≥0∞)) (fun i => ‖a k i‖ₑ)
  simp only [one_mul, one_pow, tsum_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at h
  unfold alph; refine h.trans (le_of_eq ?_); norm_num; ring

/-- **Proved.** The `ℓ²`-weighted size of `α` is controlled by the componentwise weighted norm. -/
lemma alph_weighted_le (a : FField) (w : Mode → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hs : Summable fun p : Mode × Fin 3 => w p.1 * ‖a p.1 p.2‖ ^ 2) :
    ∑' k, ENNReal.ofReal (w k) * alph a k ^ 2 ≤
      6 * ENNReal.ofReal (∑' p : Mode × Fin 3, w p.1 * ‖a p.1 p.2‖ ^ 2) := by
  rw [ENNReal.ofReal_tsum_of_nonneg (f := fun p : Mode × Fin 3 => w p.1 * ‖a p.1 p.2‖ ^ 2)
    (fun p => mul_nonneg (hw p.1) (sq_nonneg _)) hs,
    ENNReal.tsum_prod (f := fun k i => ENNReal.ofReal (w k * ‖a k i‖ ^ 2)),
    ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun k => ?_
  rw [tsum_fintype]
  calc ENNReal.ofReal (w k) * alph a k ^ 2 ≤ ENNReal.ofReal (w k) * (6 * ∑ i, ‖a k i‖ₑ ^ 2) :=
        mul_le_mul_right (alph_sq_le a k) _
    _ = 6 * ∑ i, ENNReal.ofReal (w k * ‖a k i‖ ^ 2) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]; congr 1; funext i
        rw [ENNReal.ofReal_mul (hw k), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
        ring

/-- The explicit (unoptimized) constant in `periodicH1TrilinearBound`. -/
def ladyK : ℝ := 256 * (8 * Real.pi) ^ 4 * (4 * 24000 ^ 2) * 6 ^ 6

lemma ladyK_nonneg : 0 ≤ ladyK := by unfold ladyK; positivity

/-- **Proved (discharges `PeriodicH1TrilinearBound`).** The Ladyzhenskaya-type trilinear
estimate on `T³`: for smooth periodic `v` (mean zero is not even needed), the `H¹` nonlinear
rate is summable and `max(rate, 0)⁴ ≤ ladyK · ‖v‖⁶_{H²}·‖v‖⁶_{H¹}` (squared norms cubed).
Route: pointwise Fourier bound on `N(v)` (`nlField_enorm_le`), Young `ℓ¹ * ℓ² → ℓ²`
(`enn_young`), Cauchy–Schwarz, and the Agmon/Ladyzhenskaya-type `ℓ¹` interpolation
(`enn_agmon`, via `latticeSum_le`). -/
theorem periodicH1TrilinearBound : PeriodicH1TrilinearBound ladyK := by
  intro v hv _
  set a := fourierCoeffVF v with ha
  have h1 := periodicDataHs 1 v hv
  have h2 := periodicDataHs 2 v hv
  unfold MemHsField at h1 h2
  set e := hsSq 1 v
  set x := hsSq 2 v
  have he : e = ∑' p : Mode × Fin 3, sobW 1 p.1 * ‖a p.1 p.2‖ ^ 2 := hsSq_eq_tsum 1 v
  have hx : x = ∑' p : Mode × Fin 3, sobW 2 p.1 * ‖a p.1 p.2‖ ^ 2 := hsSq_eq_tsum 2 v
  have hE : (∑' k, ENNReal.ofReal (jsq k) * alph a k ^ 2) ≤ 6 * ENNReal.ofReal e := by
    rw [he]; simp_rw [← sobW_one_jsq]
    exact alph_weighted_le a _ (fun k => (sobW_pos 1 k).le) h1
  have hX : (∑' k, ENNReal.ofReal (jsq k ^ 2) * alph a k ^ 2) ≤ 6 * ENNReal.ofReal x := by
    rw [hx]; simp_rw [← sobW_two_jsq]
    exact alph_weighted_le a _ (fun k => (sobW_pos 2 k).le) h2
  have hEf := ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) hE
  have hXf := ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) hX
  set term : Mode × Fin 3 → ℝ := fun p => sobW 1 p.1 *
    (2 * ((starRingEnd ℂ) (a p.1 p.2) * nlField a p.1 p.2).re) with hterm
  set R := ∑' k, 2 * ENNReal.ofReal (jsq k) * alph a k * ∑ i, ‖nlField a k i‖ₑ
  have hT : ∑' p, ENNReal.ofReal |term p| ≤ R := by
    rw [ENNReal.tsum_prod (f := fun k i => ENNReal.ofReal |term (k, i)|)]
    refine ENNReal.tsum_le_tsum fun k => ?_
    rw [tsum_fintype]
    calc ∑ i, ENNReal.ofReal |term (k, i)|
        ≤ ∑ i, 2 * ENNReal.ofReal (jsq k) * (‖a k i‖ₑ * ‖nlField a k i‖ₑ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hb : |term (k, i)| ≤ 2 * jsq k * (‖a k i‖ * ‖nlField a k i‖) := by
            simp only [hterm, sobW_one_jsq]
            rw [abs_mul, abs_of_pos (by linarith [one_le_jsq k] : (0:ℝ) < jsq k), abs_mul,
              abs_two]
            have := Complex.abs_re_le_norm ((starRingEnd ℂ) (a k i) * nlField a k i)
            rw [norm_mul, Complex.norm_conj] at this
            have := one_le_jsq k
            nlinarith
          refine (ENNReal.ofReal_le_ofReal hb).trans (le_of_eq ?_)
          rw [ENNReal.ofReal_mul (by linarith [one_le_jsq k]), ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm_eq_enorm, ofReal_norm_eq_enorm,
            ENNReal.ofReal_ofNat]
      _ = 2 * ENNReal.ofReal (jsq k) * ∑ i, ‖a k i‖ₑ * ‖nlField a k i‖ₑ := by rw [Finset.mul_sum]
      _ ≤ 2 * ENNReal.ofReal (jsq k) * alph a k * ∑ i, ‖nlField a k i‖ₑ := by
          rw [mul_assoc _ (alph a k)]
          refine mul_le_mul_right ?_ _
          unfold alph; rw [Finset.sum_mul]
          exact Finset.sum_le_sum fun i _ => mul_le_mul_right
            (Finset.single_le_sum (f := fun j => ‖nlField a k j‖ₑ) (fun _ _ => zero_le _)
              (Finset.mem_univ i)) _
  have hR4 := enn_trilinear a hEf hXf
  have hR4' : R ^ 4 ≤ ENNReal.ofReal (ladyK * x ^ 3 * e ^ 3) := by
    refine hR4.trans ?_
    have hx0 : 0 ≤ x := hsSq_nonneg 2 v
    have he0 : 0 ≤ e := hsSq_nonneg 1 v
    calc _ ≤ ENNReal.ofReal (256 * (8 * Real.pi) ^ 4 * (4 * 24000 ^ 2)) *
          (6 * ENNReal.ofReal x) ^ 3 * (6 * ENNReal.ofReal e) ^ 3 := by gcongr
      _ = _ := by
          rw [← ENNReal.ofReal_ofNat 6, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_pow (by positivity),
            ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1; unfold ladyK; ring
  have hRf : R ≠ ⊤ := by
    intro h; rw [h] at hR4'; simp at hR4'
  have hTf : ∑' p, ENNReal.ofReal |term p| ≠ ⊤ := ne_top_of_le_ne_top hRf hT
  have habs : Summable fun p => |term p| := by
    have := ENNReal.summable_toReal hTf
    simpa [ENNReal.toReal_ofReal (abs_nonneg _)] using this
  have hsum : Summable term := (summable_abs_iff).mp habs
  refine ⟨hsum, ?_⟩
  have hrate : rateOf 1 (nlField a) a ≤ R.toReal := by
    calc rateOf 1 (nlField a) a = ∑' p, term p := rfl
      _ ≤ ∑' p, |term p| := Summable.tsum_le_tsum (fun p => le_abs_self _) hsum habs
      _ = (∑' p, ENNReal.ofReal |term p|).toReal := by
          rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
          simp [ENNReal.toReal_ofReal (abs_nonneg _)]
      _ ≤ R.toReal := ENNReal.toReal_mono hRf hT
  have hmax : max (rateOf 1 (nlField a) a) 0 ≤ R.toReal := max_le hrate ENNReal.toReal_nonneg
  calc max (rateOf 1 (nlField a) a) 0 ^ 4 ≤ R.toReal ^ 4 :=
        pow_le_pow_left₀ (le_max_right _ _) hmax 4
    _ = (R ^ 4).toReal := (ENNReal.toReal_pow _ _).symm
    _ ≤ (ENNReal.ofReal (ladyK * x ^ 3 * e ^ 3)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hR4'
    _ = ladyK * x ^ 3 * e ^ 3 := ENNReal.toReal_ofReal (by
        have := hsSq_nonneg 2 v; have := hsSq_nonneg 1 v; have := ladyK_nonneg; positivity)

/-- **Small-`H¹`-data global continuation on `T³`, conditional only on the named
blow-up criterion `PeriodicH1BlowupCriterion ν`.** Both former hypotheses
`PeriodicH1TrilinearBound` and `PeriodicMeanConservation` are now proved. -/
theorem periodicTstar_eq_top_of_smallH1_ladyzhenskaya {ν : ℝ} (hν : 0 < ν)
    (hL : PeriodicH1BlowupCriterion ν) {u₀ : VelocityField}
    (hu₀ : IsPeriodicSmoothInitialData u₀) (hmean : ∀ i, fourierCoeffVF u₀ 0 i = 0)
    {u : TimeDependentVelocity} {p : TimeDependentPressure} (hm : IsPeriodicMaximalSolution ν u₀ u p)
    (hsmall : 8 * ladyK / (4 * Real.pi ^ 2 * ν) ^ 3 * h1Sq u₀ ^ 2 < 2 * Real.pi ^ 2 * ν) :
    periodicTstar ν u₀ = ⊤ :=
  periodicTstar_eq_top_of_smallH1_of_trilinear hν ladyK_nonneg periodicH1TrilinearBound
    (periodicMeanConservation ν) hL hu₀ hmean hm hsmall

end PeriodicNSContinuation
