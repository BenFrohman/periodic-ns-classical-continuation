/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.TimeCurve

/-!
# Spatial regularity of Fourier series with rapidly decaying coefficients

All names here are coined.
-/

noncomputable section
open Set Filter Topology MeasureTheory NavierStokes3D
open scoped ContDiff

namespace PeriodicNSContinuation

open TorusFourierNS (Mode FField)

/-- The linear phase `x ↦ 2πi k·x` on `T3` (coined). -/
def lin (k : Mode) : T3 →L[ℝ] ℂ :=
  ∑ j, (2 * Real.pi * Complex.I * ((k j : ℝ) : ℂ)) •
    (Complex.ofRealCLM.comp (EuclideanSpace.proj j))

lemma lin_apply (k : Mode) (x : T3) :
    lin k x = 2 * Real.pi * Complex.I * ∑ j, ((k j : ℝ) : ℂ) * ((x j : ℝ) : ℂ) := by
  simp only [lin, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [EuclideanSpace.proj]; ring

lemma phase_eq (k : Mode) : phase k = fun x => Complex.exp (lin k x) := by
  funext x; rw [lin_apply]; rfl

lemma norm_phase (k : Mode) (x : T3) : ‖phase k x‖ = 1 := by
  rw [phase]
  have : 2 * Real.pi * Complex.I * ∑ j, ((k j : ℝ) : ℂ) * ((x j : ℝ) : ℂ) =
      ((2 * Real.pi * ∑ j, (k j : ℝ) * x j : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma norm_lin_le (k : Mode) : ‖lin k‖ ≤ 6 * Real.pi * bse k := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by have := bse_pos k; positivity) fun x => ?_
  rw [lin_apply, norm_mul, mul_comm]
  have h2 : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    simp [abs_of_pos Real.pi_pos]
  rw [h2]
  calc ‖∑ j, ((k j : ℝ) : ℂ) * ((x j : ℝ) : ℂ)‖ * (2 * Real.pi)
      ≤ (∑ j : Fin 3, bse k * ‖x‖) * (2 * Real.pi) := by
        refine mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans
          (Finset.sum_le_sum fun j _ => ?_)) (by positivity)
        rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul (abs_int_le_bse k j) (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x j)
          (norm_nonneg _) (bse_pos k).le
    _ = 6 * Real.pi * bse k * ‖x‖ := by simp; ring

lemma hasFDerivAt_phase (k : Mode) (x : T3) :
    HasFDerivAt (phase k) (phase k x • lin k) x := by
  rw [phase_eq]
  exact (Complex.hasDerivAt_exp (lin k x)).comp_hasFDerivAt x (lin k).hasFDerivAt

lemma contDiff_phase (k : Mode) {n : WithTop ℕ∞} : ContDiff ℝ n (phase k) := by
  rw [phase_eq]; exact Complex.contDiff_exp.comp (lin k).contDiff

/-- `c ↦ c • lin k` (coined). -/
def linS (k : Mode) : ℂ →L[ℝ] (T3 →L[ℝ] ℂ) :=
  (ContinuousLinearMap.compL ℝ T3 ℂ ℂ).flip (lin k) ∘L ContinuousLinearMap.mul ℝ ℂ

lemma linS_apply (k : Mode) (c : ℂ) (v : T3) : linS k c v = c * lin k v := rfl

lemma fderiv_phase (k : Mode) : fderiv ℝ (phase k) = linS k ∘ phase k := by
  funext x; rw [(hasFDerivAt_phase k x).fderiv]; ext v; simp [linS_apply]

lemma norm_linS_le (k : Mode) : ‖linS k‖ ≤ ‖lin k‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun c => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [linS_apply, norm_mul, mul_comm ‖lin k‖, mul_assoc]
  exact mul_le_mul_of_nonneg_left ((lin k).le_opNorm v) (norm_nonneg _)

/-- **Proved.** `‖Dⁿ e^{2πik·x}‖ ≤ ‖lin k‖ⁿ`. -/
theorem norm_iteratedFDeriv_phase_le (k : Mode) (n : ℕ) (x : T3) :
    ‖iteratedFDeriv ℝ n (phase k) x‖ ≤ ‖lin k‖ ^ n := by
  induction n generalizing x with
  | zero => simp [norm_phase]
  | succ n ih =>
    rw [← norm_iteratedFDeriv_fderiv, fderiv_phase]
    refine ((linS k).norm_iteratedFDeriv_comp_left (N := ∞)
      (contDiff_phase k).contDiffAt (by exact_mod_cast le_top)).trans ?_
    rw [pow_succ']
    exact mul_le_mul (norm_linS_le k) (ih x) (norm_nonneg _) (norm_nonneg _)


/-- `(c, y) ↦ (c / wtᵣ(n)) • y_n` (coined). -/
def coordB (r : ℕ) (n : Mode) : ℂ →L[ℝ] CoefL1 →L[ℝ] (Fin 3 → ℂ) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun (c : ℂ) (y : CoefL1) => (((wt r n)⁻¹ : ℝ) * c) • (y : Mode → Fin 3 → ℂ) n)
      (fun c c' y => by simp only [mul_add, add_smul])
      (fun (t : ℝ) c y => by
        ext i; simp only [Pi.smul_apply, smul_eq_mul, mul_smul_comm, smul_mul_assoc])
      (fun c y y' => by
        simp only [lp.coeFn_add, Pi.add_apply, smul_add])
      (fun (t : ℝ) c y => by
        ext i; simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_smul_comm])) 
    (wt r n)⁻¹ fun c y => by
      simp only [LinearMap.mk₂_apply]
      rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 (wt_pos r n)), mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_apply_le_coefL1 y n) (norm_nonneg _))
        (inv_pos.2 (wt_pos r n)).le

lemma coordB_apply (r : ℕ) (n : Mode) (c : ℂ) (y : CoefL1) :
    coordB r n c y = (((wt r n)⁻¹ : ℝ) * c) • (y : Mode → Fin 3 → ℂ) n := rfl

lemma norm_coordB_le (r : ℕ) (n : Mode) : ‖coordB r n‖ ≤ (wt r n)⁻¹ :=
  LinearMap.mkContinuous₂_norm_le _ (inv_pos.2 (wt_pos r n)).le _

/-- One term of the evaluation operator (coined). -/
def evTerm (r : ℕ) (n : Mode) (x : T3) : CoefL1 →L[ℝ] (Fin 3 → ℂ) :=
  coordB r n (phase n x)

lemma norm_evTerm_iter_le (r : ℕ) (n : Mode) (m : ℕ) (x : T3) :
    ‖iteratedFDeriv ℝ m (evTerm r n) x‖ ≤ (wt r n)⁻¹ * (6 * Real.pi * bse n) ^ m := by
  have h1 := (coordB r n).norm_iteratedFDeriv_comp_left (N := ∞) (x := x)
    (contDiff_phase n).contDiffAt (n := m) (by exact_mod_cast le_top)
  refine h1.trans (mul_le_mul (norm_coordB_le r n) ?_ (norm_nonneg _) (inv_pos.2 (wt_pos r n)).le)
  exact (norm_iteratedFDeriv_phase_le n m x).trans
    (pow_le_pow_left₀ (norm_nonneg _) (norm_lin_le n) m)

lemma contDiff_evTerm (r : ℕ) (n : Mode) : ContDiff ℝ ∞ (evTerm r n) :=
  (coordB r n).contDiff.comp (contDiff_phase n)

lemma inv_wt_mul_pow_le {r m : ℕ} (h : m + 2 ≤ r) (n : Mode) :
    (wt r n)⁻¹ * (6 * Real.pi * bse n) ^ m ≤
      (6 * Real.pi) ^ m * TorusFourierNS.sobW (-2) n := by
  have hb := bse_pos n
  have h1 := one_le_bse n
  change (bse n ^ r)⁻¹ * (6 * Real.pi * bse n) ^ m ≤ (6 * Real.pi) ^ m * bse n ^ (-2 : ℝ)
  rw [Real.rpow_neg hb.le, mul_pow]
  norm_cast
  have : bse n ^ m * bse n ^ 2 ≤ bse n ^ r := by
    rw [← pow_add]; exact pow_le_pow_right₀ h1 h
  rw [inv_mul_eq_div, div_le_iff₀ (by positivity)]
  calc (6 * Real.pi) ^ m * bse n ^ m = (6 * Real.pi) ^ m * (bse n ^ 2)⁻¹ * (bse n ^ m * bse n ^ 2) := by
        field_simp
    _ ≤ (6 * Real.pi) ^ m * (bse n ^ 2)⁻¹ * bse n ^ r := by gcongr

lemma summable_inv_wt {r : ℕ} (h : 2 ≤ r) : Summable fun n => (wt r n)⁻¹ :=
  ((TorusFourierNS.summable_sobW_neg (s := 2) (by norm_num)).mul_left 1).of_nonneg_of_le
    (fun n => (inv_pos.2 (wt_pos r n)).le) fun n => by
      simpa using inv_wt_mul_pow_le (m := 0) (by omega) n

/-- The evaluation operator `y ↦ ∑ₙ e^{2πin·x} y_n / wtᵣ(n)` (coined). -/
def evOp (r : ℕ) (x : T3) : CoefL1 →L[ℝ] (Fin 3 → ℂ) := ∑' n, evTerm r n x

/-- **Proved.** `evOp r` is `C^N` in `x` when `N + 2 ≤ r`. -/
theorem contDiff_evOp {r N : ℕ} (h : N + 2 ≤ r) : ContDiff ℝ N (evOp r) := by
  unfold evOp
  refine contDiff_tsum (fun n => contDiff_infty.1 (contDiff_evTerm r n) N)
    (v := fun m n => (6 * Real.pi) ^ m * TorusFourierNS.sobW (-2) n) (fun m _ =>
      (TorusFourierNS.summable_sobW_neg (s := 2) (by norm_num)).mul_left _) fun m n x hm => ?_
  have hm' : m ≤ N := by exact_mod_cast hm
  exact (norm_evTerm_iter_le r n m x).trans (inv_wt_mul_pow_le (by omega) n)

lemma norm_evTerm_le (r : ℕ) (n : Mode) (x : T3) : ‖evTerm r n x‖ ≤ (wt r n)⁻¹ := by
  simpa using norm_evTerm_iter_le r n 0 x

lemma summable_evTerm {r : ℕ} (h : 2 ≤ r) (x : T3) : Summable fun n => evTerm r n x :=
  Summable.of_norm_bounded (summable_inv_wt h) fun n => norm_evTerm_le r n x

lemma evOp_apply {r : ℕ} (h : 2 ≤ r) (x : T3) (y : CoefL1) :
    evOp r x y = ∑' n, ((wt r n)⁻¹ * phase n x) • (y : Mode → Fin 3 → ℂ) n := by
  unfold evOp
  have := (ContinuousLinearMap.apply ℝ (Fin 3 → ℂ) y).map_tsum (summable_evTerm h x)
  simp only [ContinuousLinearMap.apply_apply] at this
  rw [this]
  exact tsum_congr fun n => rfl


/-! ### Scalar Fourier series with rapidly decaying coefficients -/

/-- `∑ ‖cₙ‖ bse(n)^p < ∞` (coined). -/
def HS (p : ℕ) (c : Mode → ℂ) : Prop := Summable fun n => ‖c n‖ * bse n ^ p

lemma HS.mono {p q : ℕ} {c : Mode → ℂ} (h : HS q c) (hpq : p ≤ q) : HS p c :=
  h.of_nonneg_of_le (fun n => by have := bse_pos n; positivity) fun n =>
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_bse n) hpq) (norm_nonneg _)

lemma HS.summable_norm {p : ℕ} {c : Mode → ℂ} (h : HS p c) : Summable fun n => ‖c n‖ :=
  (h.mono (Nat.zero_le p)).congr fun n => by simp

lemma HS.summable_term {p : ℕ} {c : Mode → ℂ} (h : HS p c) (x : T3) :
    Summable fun n => c n * phase n x :=
  Summable.of_norm (h.summable_norm.congr fun n => by rw [norm_mul, norm_phase, mul_one])

lemma HS.mul_lin {p : ℕ} {c : Mode → ℂ} (h : HS (p + 1) c) (v : T3) :
    HS p (fun n => c n * lin n v) := by
  refine ((h.mul_left (6 * Real.pi * ‖v‖))).of_nonneg_of_le
    (fun n => by have := bse_pos n; positivity) fun n => ?_
  rw [norm_mul]
  have h1 : ‖lin n v‖ ≤ 6 * Real.pi * bse n * ‖v‖ :=
    ((lin n).le_opNorm v).trans (mul_le_mul_of_nonneg_right (norm_lin_le n) (norm_nonneg _))
  have hb := bse_pos n
  calc ‖c n‖ * ‖lin n v‖ * bse n ^ p ≤ ‖c n‖ * (6 * Real.pi * bse n * ‖v‖) * bse n ^ p := by
        gcongr
    _ = 6 * Real.pi * ‖v‖ * (‖c n‖ * bse n ^ (p + 1)) := by ring

lemma HS.add {p : ℕ} {c d : Mode → ℂ} (hc : HS p c) (hd : HS p d) : HS p (c + d) :=
  (Summable.add hc hd).of_nonneg_of_le (fun n => by have := bse_pos n; positivity) fun n => by
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le (c n) (d n)) (by have := bse_pos n; positivity)

lemma HS.const_mul {p : ℕ} {c : Mode → ℂ} (hc : HS p c) (z : ℂ) : HS p (fun n => z * c n) :=
  (hc.mul_left ‖z‖).congr fun n => by rw [norm_mul, mul_assoc]

lemma norm_term_le (z : ℂ) (n : Mode) (x : T3) :
    ‖z • (phase n x • lin n)‖ ≤ 6 * Real.pi * (‖z‖ * bse n ^ 1) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by have := bse_pos n; positivity) fun v => ?_
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, norm_mul, norm_phase, one_mul, pow_one]
  have h1 : ‖lin n v‖ ≤ 6 * Real.pi * bse n * ‖v‖ :=
    ((lin n).le_opNorm v).trans (mul_le_mul_of_nonneg_right (norm_lin_le n) (norm_nonneg _))
  calc ‖z‖ * ‖lin n v‖ ≤ ‖z‖ * (6 * Real.pi * bse n * ‖v‖) := by gcongr
    _ = _ := by ring

lemma hasFDerivAt_seriesC {c : Mode → ℂ} (hc : HS 1 c) (x : T3) :
    HasFDerivAt (seriesC c) (∑' n, c n • (phase n x • lin n)) x := by
  unfold seriesC
  refine hasFDerivAt_tsum (u := fun n => 6 * Real.pi * (‖c n‖ * bse n ^ 1)) (hc.mul_left _)
    (fun n y => (hasFDerivAt_phase n y).const_mul (c n)) (fun n y => ?_)
    (hc.summable_term 0) x
  exact norm_term_le (c n) n y

lemma differentiable_seriesC {c : Mode → ℂ} (hc : HS 1 c) : Differentiable ℝ (seriesC c) :=
  fun x => (hasFDerivAt_seriesC hc x).differentiableAt

lemma fderiv_seriesC_apply {c : Mode → ℂ} (hc : HS 1 c) (x v : T3) :
    fderiv ℝ (seriesC c) x v = seriesC (fun n => c n * lin n v) x := by
  rw [(hasFDerivAt_seriesC hc x).fderiv]
  have hs : Summable fun n => c n • (phase n x • lin n) := by
    exact Summable.of_norm_bounded ((hc.mul_left (6 * Real.pi))) fun n =>
      (norm_term_le (c n) n x).trans_eq (by ring)
  have := (ContinuousLinearMap.apply ℝ ℂ v).map_tsum hs
  simp only [ContinuousLinearMap.apply_apply] at this
  rw [this]
  unfold seriesC
  refine tsum_congr fun n => ?_
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- **Proved.** Real part of a series, differentiated. -/
lemma hasFDerivAt_re_seriesC {c : Mode → ℂ} (hc : HS 1 c) (x : T3) :
    HasFDerivAt (fun y => (seriesC c y).re)
      (Complex.reCLM.comp (fderiv ℝ (seriesC c) x)) x :=
  Complex.reCLM.hasFDerivAt.comp x (differentiable_seriesC hc x).hasFDerivAt

lemma fderiv_re_seriesC_apply {c : Mode → ℂ} (hc : HS 1 c) (x v : T3) :
    fderiv ℝ (fun y => (seriesC c y).re) x v = (seriesC (fun n => c n * lin n v) x).re := by
  rw [(hasFDerivAt_re_seriesC hc x).fderiv]
  simp [fderiv_seriesC_apply hc]

lemma seriesC_add {c d : Mode → ℂ} (hc : HS 0 c) (hd : HS 0 d) (x : T3) :
    seriesC (c + d) x = seriesC c x + seriesC d x := by
  unfold seriesC
  rw [← (hc.summable_term x).tsum_add (hd.summable_term x)]
  exact tsum_congr fun n => by simp [add_mul]

lemma seriesC_const_mul {c : Mode → ℂ} (z : ℂ) (x : T3) :
    seriesC (fun n => z * c n) x = z * seriesC c x := by
  unfold seriesC
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by ring

lemma seriesC_congr {c d : Mode → ℂ} (h : ∀ n, c n = d n) : seriesC c = seriesC d := by
  rw [funext h]

lemma lin_single (n : Mode) (i : Fin 3) :
    lin n (EuclideanSpace.single i 1) = 2 * Real.pi * Complex.I * ((n i : ℝ) : ℂ) := by
  rw [lin_apply]
  congr 1
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj])
    (by simp)]
  simp

/-- **Proved.** Decay of the coefficients of an `H^{s'}`-bounded field. -/
lemma hs_of_bound {b : FField} {M : ℝ} {p : ℕ}
    (hm : TorusFourierNS.MemHsField (2 * ((p + 2 : ℕ) : ℝ)) b)
    (hn : TorusFourierNS.hsNormField (2 * ((p + 2 : ℕ) : ℝ)) b ≤ M) (i : Fin 3) :
    HS p (fun n => b n i) := by
  refine ((TorusFourierNS.summable_sobW_neg (s := 2) (by norm_num)).mul_left M).of_nonneg_of_le
    (fun n => by have := bse_pos n; positivity) fun n => ?_
  have h1 := wt_mul_norm_le hm hn n
  have h2 : ‖b n i‖ ≤ ‖b n‖ := norm_le_pi_norm (b n) i
  have hw : bse n ^ p = wt (p + 2) n * TorusFourierNS.sobW (-2) n := wt_le_mul_sobW p n
  rw [hw]
  have := TorusFourierNS.sobW_pos (-2) n
  have := wt_pos (p + 2) n
  calc ‖b n i‖ * (wt (p + 2) n * TorusFourierNS.sobW (-2) n)
      ≤ ‖b n‖ * (wt (p + 2) n * TorusFourierNS.sobW (-2) n) := by gcongr
    _ = (wt (p + 2) n * ‖b n‖) * TorusFourierNS.sobW (-2) n := by ring
    _ ≤ M * TorusFourierNS.sobW (-2) n := by gcongr


/-- Every-`H^{s'}` bound on `[0,T]` (coined). -/
def AllHsBound (T : ℝ) (a : ℝ → FField) : Prop :=
  ∀ s' : ℝ, ∃ M' : ℝ, ∀ t ∈ Icc 0 T, TorusFourierNS.MemHsField s' (a t) ∧
    TorusFourierNS.hsNormField s' (a t) ≤ M'

lemma AllHsBound.hs {T : ℝ} {a : ℝ → FField} (h : AllHsBound T a) {t : ℝ} (ht : t ∈ Icc 0 T)
    (p : ℕ) (i : Fin 3) : HS p (fun n => a t n i) := by
  obtain ⟨M, hM⟩ := h (2 * ((p + 2 : ℕ) : ℝ))
  exact hs_of_bound (hM t ht).1 (hM t ht).2 i

lemma seriesVelocity_apply (a : ℝ → FField) (t : ℝ) (x : T3) (i : Fin 3) :
    seriesVelocity a t x i = (seriesC (fun n => a t n i) x).re := rfl

lemma seriesC_zero (x : T3) : seriesC (fun _ => 0) x = 0 := by simp [seriesC]

lemma seriesC_sum3 {c : Fin 3 → Mode → ℂ} (hc : ∀ i, HS 0 (c i)) (x : T3) :
    ∑ i, seriesC (c i) x = seriesC (fun n => ∑ i, c i n) x := by
  rw [Fin.sum_univ_three, ← seriesC_add (hc 0) (hc 1), ← seriesC_add ((hc 0).add (hc 1)) (hc 2)]
  congr 1; funext n; simp [Fin.sum_univ_three]

/-- **Proved.** A divergence-free coefficient family gives a divergence-free series velocity. -/
theorem div_seriesVelocity {T : ℝ} {a : ℝ → FField} (h : AllHsBound T a) {t : ℝ}
    (ht : t ∈ Icc 0 T) (hdiv : TorusFourierNS.DivergenceFree (a t)) (x : T3) :
    div (seriesVelocity a t) x = 0 := by
  unfold div
  simp only [seriesVelocity_apply]
  simp only [fderiv_re_seriesC_apply (h.hs ht 1 _)]
  rw [← Complex.re_sum, seriesC_sum3 fun i => (h.hs ht 1 i).mul_lin _]
  have : ∀ n, ∑ i, a t n i * lin n (EuclideanSpace.single i 1) =
      2 * Real.pi * Complex.I * TorusFourierNS.dot (TorusFourierNS.kvec n) (a t n) := fun n => by
    simp only [lin_single, TorusFourierNS.dot, TorusFourierNS.kvec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [this, hdiv _, mul_zero, seriesC_zero, Complex.zero_re]

/-- Real part, componentwise, as a continuous linear map (coined). -/
def reVec : (Fin 3 → ℂ) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => Complex.reCLM.comp (ContinuousLinearMap.proj i))

lemma reVec_apply (w : Fin 3 → ℂ) (i : Fin 3) : reVec w i = (w i).re := rfl

lemma seriesVelocity_eq_evOp {ν T : ℝ} {a : ℝ → FField} (h : CurveHyp ν T a) {r : ℕ} (hr : 2 ≤ r)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : T3) :
    seriesVelocity a t x = reVec (evOp r x (coefCurve r a t)) := by
  ext i
  rw [seriesVelocity_apply, reVec_apply, evOp_apply hr]
  have hs : Summable fun n =>
      (((wt r n)⁻¹ : ℝ) * phase n x) • ((coefCurve r a t : CoefL1) : Mode → Fin 3 → ℂ) n :=
    (summable_evTerm hr x).map (ContinuousLinearMap.apply ℝ (Fin 3 → ℂ) (coefCurve r a t))
      (ContinuousLinearMap.continuous _) |>.congr fun n => rfl
  have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℂ) i).map_tsum hs
  simp only [ContinuousLinearMap.proj_apply] at this
  rw [this]
  congr 1
  unfold seriesC
  refine tsum_congr fun n => ?_
  rw [h.coefCurve_apply r ht n]
  simp only [Pi.smul_apply, smul_eq_mul]
  have : (wt r n : ℂ) ≠ 0 := by exact_mod_cast (wt_pos r n).ne'
  push_cast
  field_simp


/-- **Proved.** Joint `C^∞` regularity of the series velocity on `[0,T] × T3`, under `CurveHyp`. -/
theorem CurveHyp.contDiffOn_seriesVelocity {ν T : ℝ} {a : ℝ → FField} (h : CurveHyp ν T a)
    (hT : 0 < T) :
    ContDiffOn ℝ ∞ (fun q : ℝ × T3 => seriesVelocity a q.1 q.2) (Icc (0 : ℝ) T ×ˢ univ) := by
  refine _root_.contDiffOn_infty.2 fun N => ?_
  have hE : ContDiffOn ℝ N (fun q : ℝ × T3 => evOp (N + 2) q.2) (Icc (0 : ℝ) T ×ˢ univ) :=
    ((contDiff_evOp le_rfl).comp contDiff_snd).contDiffOn
  have hc : ContDiffOn ℝ N (fun q : ℝ × T3 => coefCurve (N + 2) a q.1) (Icc (0 : ℝ) T ×ˢ univ) :=
    (h.contDiffOn hT N (N + 2)).comp contDiff_fst.contDiffOn fun q hq => hq.1
  refine (reVec.contDiff.comp_contDiffOn (hE.clm_apply hc)).congr fun q hq => ?_
  exact seriesVelocity_eq_evOp h (by omega) hq.1 q.2

end PeriodicNSContinuation
