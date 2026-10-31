/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.GalerkinLimitProof
import PeriodicNSContinuation.Reconstruction

/-!
# The coefficient space `ℓ¹(ℤ³; ℂ³)` and the Navier–Stokes nonlinearity on it

All names here are coined.
-/

noncomputable section
open Set Filter Topology MeasureTheory

namespace PeriodicNSContinuation

open TorusFourierNS (Mode FField)

/-- `ℓ¹(ℤ³; ℂ³)` (coined). -/
abbrev CoefL1 := lp (fun _ : Mode => Fin 3 → ℂ) 1

lemma norm_coefL1 (x : CoefL1) : ‖x‖ = ∑' k, ‖x k‖ := by
  rw [lp.norm_eq_tsum_rpow (by simp)]; simp

lemma summable_norm_coefL1 (x : CoefL1) : Summable fun k => ‖x k‖ := by
  simpa using (lp.memℓp x).summable (by simp)

lemma norm_apply_le_coefL1 (x : CoefL1) (k : Mode) : ‖x k‖ ≤ ‖x‖ :=
  lp.norm_apply_le_norm one_ne_zero x k

lemma memCoefL1 {f : Mode → Fin 3 → ℂ} (h : Summable fun k => ‖f k‖) :
    Memℓp f 1 := memℓp_gen (by simpa using h)

/-- An element of `CoefL1` from a summable family (coined). -/
def mkL1 (f : Mode → Fin 3 → ℂ) (h : Summable fun k => ‖f k‖) : CoefL1 := ⟨f, memCoefL1 h⟩

@[simp] lemma mkL1_apply (f : Mode → Fin 3 → ℂ) (h) (k : Mode) : mkL1 f h k = f k := rfl

lemma norm_mkL1 (f : Mode → Fin 3 → ℂ) (h) : ‖mkL1 f h‖ = ∑' k, ‖f k‖ := norm_coefL1 _

/-- Fiberwise bounded multiplier on `CoefL1` (coined). -/
def mulOp (M : Mode → (Fin 3 → ℂ) →ₗ[ℝ] (Fin 3 → ℂ)) (C : ℝ)
    (hM : ∀ k w, ‖M k w‖ ≤ C * ‖w‖) : CoefL1 →L[ℝ] CoefL1 :=
  LinearMap.mkContinuous
    { toFun := fun x => mkL1 (fun k => M k (x k)) (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun k => hM k (x k)) ((summable_norm_coefL1 x).mul_left C))
      map_add' := fun x y => lp.ext <| funext fun k => by
        simp only [lp.coeFn_add, Pi.add_apply, mkL1_apply, map_add]
      map_smul' := fun c x => lp.ext <| funext fun k => by
        simp only [lp.coeFn_smul, Pi.smul_apply, mkL1_apply, map_smul, RingHom.id_apply]; rfl }
    C (fun x => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, norm_mkL1]
      rw [norm_coefL1, ← tsum_mul_left]
      exact Summable.tsum_le_tsum (fun k => hM k (x k))
        (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => hM k (x k))
          ((summable_norm_coefL1 x).mul_left C)) ((summable_norm_coefL1 x).mul_left C))

@[simp] lemma mulOp_apply (M : Mode → (Fin 3 → ℂ) →ₗ[ℝ] (Fin 3 → ℂ)) (C hM) (x : CoefL1)
    (k : Mode) : mulOp M C hM x k = M k (x k) := rfl

/-- **Proved.** Discrete convolution of nonnegative summable families on `ℤ³`. -/
theorem summable_conv_nonneg {f g : Mode → ℝ} (hf : Summable f) (hg : Summable g)
    (hf0 : ∀ k, 0 ≤ f k) (hg0 : ∀ k, 0 ≤ g k) :
    Summable (fun p : Mode × Mode => f p.2 * g (p.1 - p.2)) ∧
    Summable (fun k => ∑' m, f m * g (k - m)) ∧
    ∑' k, ∑' m, f m * g (k - m) = (∑' k, f k) * ∑' k, g k := by
  have hp : Summable (fun z : Mode × Mode => f z.1 * g z.2) :=
    Summable.mul_of_nonneg hf hg (fun k => hf0 k) (fun k => hg0 k)
  let e : Mode × Mode ≃ Mode × Mode :=
    { toFun := fun p => (p.2, p.1 - p.2), invFun := fun q => (q.1 + q.2, q.1),
      left_inv := fun p => by simp, right_inv := fun q => by simp }
  have hq : Summable (fun p : Mode × Mode => f p.2 * g (p.1 - p.2)) :=
    (e.summable_iff (f := fun z : Mode × Mode => f z.1 * g z.2)).2 hp
  refine ⟨hq, hq.prod, ?_⟩
  rw [← hq.tsum_prod, tsum_mul_tsum_of_summable_norm (by simpa [Real.norm_of_nonneg (hf0 _)] using hf)
    (by simpa [Real.norm_of_nonneg (hg0 _)] using hg)]
  exact e.tsum_eq (fun z : Mode × Mode => f z.1 * g z.2)


/-- Weight `(1+|k|²)^r` (coined). -/
def wt (r : ℕ) (k : Mode) : ℝ := bse k ^ r

lemma wt_pos (r : ℕ) (k : Mode) : 0 < wt r k := pow_pos (bse_pos k) r

lemma one_le_wt (r : ℕ) (k : Mode) : 1 ≤ wt r k := one_le_pow₀ (one_le_bse k)

/-- Unweighting: `x_k / (1+|k|²)^r` (coined). -/
def unw (r : ℕ) (x : CoefL1) : FField := fun k i => x k i / (wt r k : ℂ)

lemma abs_int_le_bse (n : Mode) (l : Fin 3) : |((n l : ℤ) : ℝ)| ≤ bse n := by
  have h1 : |((n l : ℤ) : ℝ)| ≤ ((n l : ℤ) : ℝ) ^ 2 := by
    rcases eq_or_ne (n l) 0 with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ |((n l : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h
      rw [← sq_abs]; nlinarith
  have h2 := Finset.single_le_sum (f := fun i => ((n i : ℝ)) ^ 2) (fun i _ => sq_nonneg _)
    (Finset.mem_univ l)
  unfold bse; simp only at h2; linarith

lemma bse_neg_sub (k m : Mode) : bse (m - k) = bse (k - m) := by
  unfold bse; congr 1; refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply, Int.cast_sub]; ring

/-- Bilinear convolution term on unweighted fields (coined). -/
def cterm (u v : FField) (k m : Mode) (j : Fin 3) : ℂ :=
  (∑ l, u m l * ((((k - m) l : ℤ)) : ℂ)) * v (k - m) j

lemma cterm_self (a : FField) (k m : Mode) (j : Fin 3) : cterm a a k m j = convTerm a k m j := rfl

lemma norm_unw_le (r : ℕ) (x : CoefL1) (k : Mode) (i : Fin 3) :
    ‖unw r x k i‖ ≤ ‖x k‖ / wt r k := by
  unfold unw
  rw [norm_div, Complex.norm_of_nonneg (wt_pos r k).le]
  exact div_le_div_of_nonneg_right (norm_le_pi_norm (x k) i) (wt_pos r k).le

/-- **Proved.** Pointwise weighted bound on the convolution term. -/
theorem wt_mul_norm_cterm_le (r : ℕ) (x y : CoefL1) (k m : Mode) (j : Fin 3) :
    wt r k * ‖cterm (unw (r + 2) x) (unw (r + 2) y) k m j‖ ≤
      3 * 2 ^ r * (‖x m‖ * ‖y (k - m)‖) := by
  set A := ‖x m‖; set B := ‖y (k - m)‖
  set bm := bse m; set bd := bse (k - m)
  have hbm : 1 ≤ bm := one_le_bse m
  have hbd : 1 ≤ bd := one_le_bse (k - m)
  have hA : 0 ≤ A := norm_nonneg _
  have hB : 0 ≤ B := norm_nonneg _
  have h1 : ‖∑ l, unw (r + 2) x m l * ((((k - m) l : ℤ)) : ℂ)‖ ≤ 3 * (A / bm ^ (r + 2) * bd) := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ l ∈ Finset.univ, ‖unw (r + 2) x m l * ((((k - m) l : ℤ)) : ℂ)‖ ≤
        A / bm ^ (r + 2) * bd := by
      intro l _
      rw [norm_mul]
      refine mul_le_mul (norm_unw_le _ _ _ _) ?_ (norm_nonneg _) (by positivity)
      rw [Complex.norm_intCast]; exact abs_int_le_bse _ _
    refine (Finset.sum_le_sum this).trans ?_
    simp
  have h2 : ‖unw (r + 2) y (k - m) j‖ ≤ B / bd ^ (r + 2) := norm_unw_le _ _ _ _
  have h3 : wt r k ≤ 2 ^ r * bm ^ r * bd ^ r := by
    unfold wt
    have := bse_le m k
    rw [bse_neg_sub] at this
    calc bse k ^ r ≤ (2 * bm * bd) ^ r := pow_le_pow_left₀ (bse_pos k).le this r
      _ = _ := by ring
  unfold cterm
  rw [norm_mul]
  have hbm0 : 0 < bm := by linarith
  have hbd0 : 0 < bd := by linarith
  calc wt r k * (‖∑ l, unw (r + 2) x m l * ((((k - m) l : ℤ)) : ℂ)‖ * ‖unw (r + 2) y (k - m) j‖)
      ≤ (2 ^ r * bm ^ r * bd ^ r) * (3 * (A / bm ^ (r + 2) * bd) * (B / bd ^ (r + 2))) := by
        gcongr
    _ = 3 * 2 ^ r * (A * B) * (1 / (bm ^ 2 * bd)) := by
        field_simp
        ring
    _ ≤ 3 * 2 ^ r * (A * B) := by
        refine mul_le_of_le_one_right (by positivity) ?_
        rw [div_le_one (by positivity)]
        nlinarith [one_le_pow₀ (n := 2) hbm]

lemma summable_cterm (r : ℕ) (x y : CoefL1) (k : Mode) (j : Fin 3) :
    Summable fun m => ‖cterm (unw (r + 2) x) (unw (r + 2) y) k m j‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    (((summable_norm_coefL1 x).mul_right (‖y‖)).mul_left (3 * 2 ^ r))
  have h := wt_mul_norm_cterm_le r x y k m j
  have hw := one_le_wt r k
  have : 3 * 2 ^ r * (‖x m‖ * ‖y (k - m)‖) ≤ 3 * 2 ^ r * (‖x m‖ * ‖y‖) := by
    gcongr; exact norm_apply_le_coefL1 _ _
  nlinarith [norm_nonneg (cterm (unw (r + 2) x) (unw (r + 2) y) k m j)]

lemma summable_conv_xy (x y : CoefL1) (k : Mode) :
    Summable fun m => ‖x m‖ * ‖y (k - m)‖ :=
  Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun m => mul_le_mul_of_nonneg_left (norm_apply_le_coefL1 _ _) (norm_nonneg _))
    ((summable_norm_coefL1 x).mul_right _)

/-- Weighted nonlinearity, raw family (coined). -/
def bilRaw (r : ℕ) (x y : CoefL1) (k : Mode) : Fin 3 → ℂ := fun j =>
  (wt r k : ℂ) * (2 * Real.pi * Complex.I * ∑' m, cterm (unw (r + 2) x) (unw (r + 2) y) k m j)

lemma norm_bilRaw_le (r : ℕ) (x y : CoefL1) (k : Mode) :
    ‖bilRaw r x y k‖ ≤ 2 * Real.pi * (3 * 2 ^ r) * ∑' m, ‖x m‖ * ‖y (k - m)‖ := by
  have h0 : (0 : ℝ) ≤ ∑' m, ‖x m‖ * ‖y (k - m)‖ :=
    tsum_nonneg fun m => mul_nonneg (norm_nonneg (x m)) (norm_nonneg (y (k - m)))
  refine pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun j => ?_
  unfold bilRaw
  rw [norm_mul, norm_mul, Complex.norm_of_nonneg (wt_pos r k).le]
  have h2 : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    simp [Real.pi_pos.le]
  rw [h2]
  have h3 : wt r k * ‖∑' m, cterm (unw (r + 2) x) (unw (r + 2) y) k m j‖ ≤
      (3 * 2 ^ r) * ∑' m, ‖x m‖ * ‖y (k - m)‖ := by
    refine (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (summable_cterm r x y k j))
      (wt_pos r k).le).trans ?_
    rw [← tsum_mul_left, ← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun m => wt_mul_norm_cterm_le r x y k m j)
      ((summable_cterm r x y k j).mul_left _) ((summable_conv_xy x y k).mul_left _)
  nlinarith [Real.pi_pos]

lemma conv_facts (x y : CoefL1) :
    Summable (fun k => ∑' m, ‖x m‖ * ‖y (k - m)‖) ∧
    ∑' k, ∑' m, ‖x m‖ * ‖y (k - m)‖ = ‖x‖ * ‖y‖ := by
  obtain ⟨-, h1, h2⟩ := summable_conv_nonneg (summable_norm_coefL1 x) (summable_norm_coefL1 y)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  exact ⟨h1, by rw [h2, ← norm_coefL1, ← norm_coefL1]⟩

lemma summable_bilRaw (r : ℕ) (x y : CoefL1) : Summable fun k => ‖bilRaw r x y k‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_bilRaw_le r x y)
    ((conv_facts x y).1.mul_left _)

lemma unw_add (r : ℕ) (x x' : CoefL1) : unw r (x + x') = unw r x + unw r x' := by
  funext k i; simp only [unw, lp.coeFn_add, Pi.add_apply, add_div]

lemma unw_smul (r : ℕ) (c : ℝ) (x : CoefL1) : unw r (c • x) = fun k i => (c : ℂ) * unw r x k i := by
  funext k i; simp only [unw, lp.coeFn_smul, Pi.smul_apply]; change (c : ℂ) * _ / _ = _; ring

lemma cterm_add_left (u u' v : FField) (k m j) :
    cterm (u + u') v k m j = cterm u v k m j + cterm u' v k m j := by
  simp [cterm, add_mul, Finset.sum_add_distrib]

lemma cterm_add_right (u v v' : FField) (k m j) :
    cterm u (v + v') k m j = cterm u v k m j + cterm u v' k m j := by
  simp [cterm, mul_add]

lemma cterm_smul_left (c : ℂ) (u v : FField) (k m j) :
    cterm (fun k i => c * u k i) v k m j = c * cterm u v k m j := by
  simp only [cterm, mul_assoc, ← Finset.mul_sum]

lemma cterm_smul_right (c : ℂ) (u v : FField) (k m j) :
    cterm u (fun k i => c * v k i) k m j = c * cterm u v k m j := by
  simp only [cterm]; ring

/-- Weighted nonlinearity as a bounded bilinear map (coined). -/
def bilOp (r : ℕ) : CoefL1 →L[ℝ] CoefL1 →L[ℝ] CoefL1 :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun x y => mkL1 (bilRaw r x y) (summable_bilRaw r x y))
      (fun x x' y => lp.ext <| funext fun k => funext fun j => by
        simp only [mkL1_apply, lp.coeFn_add, Pi.add_apply, bilRaw, unw_add, cterm_add_left]
        rw [Summable.tsum_add (summable_cterm r x y k j).of_norm
          (summable_cterm r x' y k j).of_norm]; ring)
      (fun c x y => lp.ext <| funext fun k => funext fun j => by
        simp only [mkL1_apply, lp.coeFn_smul, Pi.smul_apply, bilRaw, unw_smul, cterm_smul_left]
        rw [tsum_mul_left]; change _ = (c : ℂ) * _; ring)
      (fun x y y' => lp.ext <| funext fun k => funext fun j => by
        simp only [mkL1_apply, lp.coeFn_add, Pi.add_apply, bilRaw, unw_add, cterm_add_right]
        rw [Summable.tsum_add (summable_cterm r x y k j).of_norm
          (summable_cterm r x y' k j).of_norm]; ring)
      (fun c x y => lp.ext <| funext fun k => funext fun j => by
        simp only [mkL1_apply, lp.coeFn_smul, Pi.smul_apply, bilRaw, unw_smul, cterm_smul_right]
        rw [tsum_mul_left]; change _ = (c : ℂ) * _; ring))
    (2 * Real.pi * (3 * 2 ^ r)) (fun x y => by
      simp only [LinearMap.mk₂_apply, norm_mkL1]
      rw [mul_assoc, ← (conv_facts x y).2, ← tsum_mul_left]
      exact Summable.tsum_le_tsum (norm_bilRaw_le r x y) (summable_bilRaw r x y)
        ((conv_facts x y).1.mul_left _))

@[simp] lemma bilOp_apply (r : ℕ) (x y : CoefL1) (k : Mode) :
    bilOp r x y k = bilRaw r x y k := rfl


/-! ### Multipliers -/

lemma ksq_le_bse (k : Mode) : TorusFourierNS.ksq (TorusFourierNS.kvec k) ≤ bse k := by
  unfold TorusFourierNS.ksq TorusFourierNS.kvec bse; linarith

lemma ksq_nonneg' (k : Mode) : 0 ≤ TorusFourierNS.ksq (TorusFourierNS.kvec k) :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Viscous multiplier `-4π²ν|k|² (1+|k|²)^{-2}` (coined). -/
def viscMul (ν : ℝ) (r : ℕ) (k : Mode) : ℝ :=
  -TorusFourierNS.viscCoeff ν k * wt r k / wt (r + 2) k

lemma abs_viscMul_le (ν : ℝ) (r : ℕ) (k : Mode) : |viscMul ν r k| ≤ 4 * Real.pi ^ 2 * |ν| := by
  unfold viscMul TorusFourierNS.viscCoeff
  have hb := one_le_bse k
  have hq := ksq_le_bse k
  have hq0 := ksq_nonneg' k
  have hw : wt (r + 2) k = wt r k * bse k ^ 2 := by unfold wt; ring
  rw [hw, abs_div, abs_mul, abs_neg, abs_mul, abs_mul, abs_of_nonneg (wt_pos r k).le,
    abs_of_nonneg hq0, abs_of_pos (by positivity : (0:ℝ) < 4 * Real.pi ^ 2),
    abs_of_pos (mul_pos (wt_pos r k) (pow_pos (bse_pos k) 2))]
  rw [div_le_iff₀ (mul_pos (wt_pos r k) (pow_pos (bse_pos k) 2))]
  have h1 : TorusFourierNS.ksq (TorusFourierNS.kvec k) ≤ bse k ^ 2 := by nlinarith
  have := wt_pos r k
  have : 0 ≤ 4 * Real.pi ^ 2 * |ν| := by positivity
  calc 4 * Real.pi ^ 2 * |ν| * TorusFourierNS.ksq (TorusFourierNS.kvec k) * wt r k
      ≤ 4 * Real.pi ^ 2 * |ν| * bse k ^ 2 * wt r k := by gcongr
    _ = _ := by ring

/-- Viscous operator on `CoefL1` (coined). -/
def viscOp (ν : ℝ) (r : ℕ) : CoefL1 →L[ℝ] CoefL1 :=
  mulOp (fun k => viscMul ν r k • LinearMap.id) (4 * Real.pi ^ 2 * |ν|) (fun k w => by
    simp only [LinearMap.smul_apply, LinearMap.id_apply, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_viscMul_le ν r k) (norm_nonneg w))

/-- Leray projector as an `ℝ`-linear map (coined). -/
def lerayLin (k : Mode) : (Fin 3 → ℂ) →ₗ[ℝ] (Fin 3 → ℂ) where
  toFun := TorusFourierNS.lerayP k
  map_add' := TorusFourierNS.lerayP_add k
  map_smul' := TorusFourierNS.lerayP_smul k

lemma norm_lerayP_le' (k : Mode) (w : Fin 3 → ℂ) : ‖TorusFourierNS.lerayP k w‖ ≤ 6 * ‖w‖ := by
  refine pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun i => (norm_lerayP_le k w i).trans ?_
  have : ∑ j, ‖w j‖ ≤ ∑ _j : Fin 3, ‖w‖ := Finset.sum_le_sum fun j _ => norm_le_pi_norm w j
  simp at this; linarith

/-- Leray operator on `CoefL1` (coined). -/
def lerayOp : CoefL1 →L[ℝ] CoefL1 := mulOp lerayLin 6 norm_lerayP_le'

lemma pressureCoeff_add (k : Mode) (w w' : Fin 3 → ℂ) :
    pressureCoeff k (w + w') = pressureCoeff k w + pressureCoeff k w' := by
  simp only [pressureCoeff, TorusFourierNS.dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

lemma pressureCoeff_smul (k : Mode) (c : ℂ) (w : Fin 3 → ℂ) :
    pressureCoeff k (c • w) = c * pressureCoeff k w := by
  simp only [pressureCoeff, TorusFourierNS.dot, Pi.smul_apply, smul_eq_mul]
  rw [show ∑ i, ((TorusFourierNS.kvec k i : ℝ) : ℂ) * (c * w i) =
    c * ∑ i, ((TorusFourierNS.kvec k i : ℝ) : ℂ) * w i by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
  ring

lemma pressureCoeff_smul_real (k : Mode) (c : ℝ) (w : Fin 3 → ℂ) :
    pressureCoeff k (c • w) = c * pressureCoeff k w := by
  have : c • w = (c : ℂ) • w := by funext i; simp [Complex.real_smul]
  rw [this, pressureCoeff_smul]

lemma norm_pressureCoeff_le (k : Mode) (w : Fin 3 → ℂ) : ‖pressureCoeff k w‖ ≤ ‖w‖ := by
  unfold pressureCoeff
  set q := TorusFourierNS.ksq (TorusFourierNS.kvec k)
  have hq0 : 0 ≤ q := ksq_nonneg' k
  rcases hq0.eq_or_lt with h | h
  · rw [← h]; simp
  · rw [norm_div, norm_neg, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Complex.norm_real, Complex.norm_I, Real.norm_of_nonneg Real.pi_pos.le, Real.norm_of_nonneg h.le]
    rw [div_le_iff₀ (by positivity)]
    have hd : ‖TorusFourierNS.dot (TorusFourierNS.kvec k) w‖ ≤ ∑ i : Fin 3, q * ‖w‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul, Complex.norm_real]
      refine mul_le_mul ?_ (norm_le_pi_norm w i) (norm_nonneg _) hq0
      have h1 := abs_int_le_bse k i
      have h2 : |((k i : ℤ) : ℝ)| ≤ ((k i : ℤ) : ℝ) ^ 2 := by
        rcases eq_or_ne (k i) 0 with h | h
        · simp [h]
        · have : (1 : ℝ) ≤ |((k i : ℤ) : ℝ)| := by
            rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h
          rw [← sq_abs]; nlinarith
      have h3 := Finset.single_le_sum (f := fun i => (TorusFourierNS.kvec k i) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ i)
      simp only [Real.norm_eq_abs, TorusFourierNS.kvec] at h3 ⊢
      exact h2.trans h3
    simp at hd
    have : 3 * (q * ‖w‖) ≤ ‖w‖ * (2 * Real.pi * 1 * q) := by
      nlinarith [mul_nonneg h.le (norm_nonneg w), Real.pi_gt_three]
    linarith

/-- Pressure coefficient map, copied into all three slots (coined). -/
def pressLin (k : Mode) : (Fin 3 → ℂ) →ₗ[ℝ] (Fin 3 → ℂ) where
  toFun w := fun _ => pressureCoeff k w
  map_add' w w' := by funext i; simp [pressureCoeff_add]
  map_smul' c w := by
    funext i; simp only [Pi.smul_apply, RingHom.id_apply]
    exact (pressureCoeff_smul_real k c w).trans Complex.real_smul.symm

/-- Pressure operator on `CoefL1` (coined). -/
def pressOp : CoefL1 →L[ℝ] CoefL1 := mulOp pressLin 1 (fun k w => by
  refine pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun _ => ?_
  simpa [pressLin] using norm_pressureCoeff_le k w)

/-! ### Weighted embedding -/

open Classical in
/-- Weighted embedding `a ↦ ((1+|k|²)^r a_k)_k`, zero if not summable (coined). -/
def emb (r : ℕ) (a : FField) : CoefL1 :=
  if h : Summable (fun k => ‖fun i => (wt r k : ℂ) * a k i‖) then mkL1 _ h else 0

lemma emb_apply {r : ℕ} {a : FField} (h : Summable (fun k => ‖fun i => (wt r k : ℂ) * a k i‖))
    (k : Mode) (i : Fin 3) : emb r a k i = wt r k * a k i := by
  simp [emb, h]

lemma emb_eq {r : ℕ} {a : FField} (x : CoefL1) (hx : ∀ k i, x k i = wt r k * a k i) :
    emb r a = x := by
  have h : Summable (fun k => ‖fun i => (wt r k : ℂ) * a k i‖) := by
    have : (fun k => ‖fun i => (wt r k : ℂ) * a k i‖) = fun k => ‖x k‖ := by
      funext k; congr 1; funext i; exact (hx k i).symm
    rw [this]; exact summable_norm_coefL1 x
  ext k i; rw [emb_apply h, hx]

lemma unw_emb {r : ℕ} {a : FField} (h : Summable (fun k => ‖fun i => (wt r k : ℂ) * a k i‖)) :
    unw r (emb r a) = a := by
  funext k i; rw [unw, emb_apply h]
  have : (wt r k : ℂ) ≠ 0 := by exact_mod_cast (wt_pos r k).ne'
  field_simp

/-- Weighted NS vector field on `CoefL1` (coined). -/
def nsOp (ν : ℝ) (r : ℕ) (x : CoefL1) : CoefL1 := viscOp ν r x - lerayOp (bilOp r x x)

lemma contDiff_nsOp (ν : ℝ) (r : ℕ) : ContDiff ℝ ⊤ (nsOp ν r) :=
  (viscOp ν r).contDiff.sub (lerayOp.contDiff.comp ((bilOp r).contDiff.clm_apply contDiff_id))

lemma bilRaw_emb {r : ℕ} {a : FField}
    (h : Summable (fun k => ‖fun i => (wt (r + 2) k : ℂ) * a k i‖)) (k : Mode) :
    bilRaw r (emb (r + 2) a) (emb (r + 2) a) k = (wt r k : ℝ) • nonlinCoeff a k := by
  funext j
  simp only [bilRaw, unw_emb h, cterm_self, nonlinCoeff, Pi.smul_apply, Complex.real_smul]

lemma nsOp_emb_coord {ν : ℝ} {r : ℕ} {a : FField}
    (h : Summable (fun k => ‖fun i => (wt (r + 2) k : ℂ) * a k i‖)) (k : Mode) (i : Fin 3) :
    nsOp ν r (emb (r + 2) a) k i = wt r k * fourierNSField ν a k i := by
  have hF : fourierNSField ν a k i = -((TorusFourierNS.viscCoeff ν k : ℝ) : ℂ) * a k i -
      TorusFourierNS.lerayP k (nonlinCoeff a k) i := rfl
  rw [hF]
  simp only [nsOp, lp.coeFn_sub, Pi.sub_apply, viscOp, lerayOp, mulOp_apply, bilOp_apply,
    LinearMap.smul_apply, LinearMap.id_apply, lerayLin, LinearMap.coe_mk, AddHom.coe_mk,
    bilRaw_emb h, TorusFourierNS.lerayP_smul, Pi.smul_apply, emb_apply h,
    viscMul, Complex.real_smul]
  have : (wt (r + 2) k : ℂ) ≠ 0 := by exact_mod_cast (wt_pos (r + 2) k).ne'
  have e : ∀ (c : ℝ) (z : ℂ), c • z = (c : ℂ) * z := fun c z => Complex.real_smul
  erw [e]
  push_cast
  field_simp

/-- **Proved.** The weighted NS operator represents `fourierNSField`. -/
theorem nsOp_emb {ν : ℝ} {r : ℕ} {a : FField}
    (h : Summable (fun k => ‖fun i => (wt (r + 2) k : ℂ) * a k i‖)) :
    nsOp ν r (emb (r + 2) a) = emb r (fourierNSField ν a) :=
  (emb_eq _ (nsOp_emb_coord h)).symm

lemma pressOp_bil_emb {r : ℕ} {a : FField}
    (h : Summable (fun k => ‖fun i => (wt (r + 2) k : ℂ) * a k i‖)) (k : Mode) (i : Fin 3) :
    pressOp (bilOp r (emb (r + 2) a) (emb (r + 2) a)) k i =
      wt r k * pressureCoeff k (nonlinCoeff a k) := by
  simp only [pressOp, mulOp_apply, bilOp_apply, pressLin, LinearMap.coe_mk, AddHom.coe_mk,
    bilRaw_emb h]
  rw [pressureCoeff_smul_real]

end PeriodicNSContinuation
