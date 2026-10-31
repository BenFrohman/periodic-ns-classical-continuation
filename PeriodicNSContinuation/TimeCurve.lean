/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.CoefSpace
import PeriodicNSContinuation.Clamp

/-!
# Time regularity of the weighted coefficient curve

All names here are coined.
-/

noncomputable section
open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace PeriodicNSContinuation

open TorusFourierNS (Mode FField)
open Clamp

lemma sobW_two_mul (r : ℕ) (k : Mode) : TorusFourierNS.sobW (2 * (r : ℝ)) k = wt r k ^ 2 := by
  change bse k ^ (2 * (r : ℝ)) = (bse k ^ r) ^ 2
  rw [mul_comm, Real.rpow_mul (bse_pos k).le]; norm_cast

/-- Pointwise bound from an `H^{2r}` bound. -/
lemma wt_mul_norm_le {r : ℕ} {b : FField} {M : ℝ} (hm : TorusFourierNS.MemHsField (2 * (r : ℝ)) b)
    (hn : TorusFourierNS.hsNormField (2 * (r : ℝ)) b ≤ M) (k : Mode) : wt r k * ‖b k‖ ≤ M := by
  have hM : 0 ≤ M := le_trans (Real.sqrt_nonneg _) hn
  have hT : (∑' p : Mode × Fin 3, TorusFourierNS.sobW (2 * (r : ℝ)) p.1 * ‖b p.1 p.2‖ ^ 2)
      ≤ M ^ 2 := by
    rw [← Real.sq_sqrt (tsum_nonneg fun p => by
      have := TorusFourierNS.sobW_pos (2 * (r : ℝ)) p.1; positivity)]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hn 2
  have hw := wt_pos r k
  rw [← le_div_iff₀' hw]
  refine (pi_norm_le_iff_of_nonneg (div_nonneg hM hw.le)).2 fun i => ?_
  rw [le_div_iff₀' hw]
  have h1 := (hm.le_tsum (k, i) fun p _ => by
    have := TorusFourierNS.sobW_pos (2 * (r : ℝ)) p.1; positivity).trans hT
  simp only [sobW_two_mul] at h1
  rw [← mul_pow] at h1
  exact (pow_le_pow_iff_left₀ (by positivity) hM two_ne_zero).1 h1

lemma norm_wt_fun (r : ℕ) (b : FField) (k : Mode) :
    ‖fun i => (wt r k : ℂ) * b k i‖ = wt r k * ‖b k‖ := by
  have : (fun i => (wt r k : ℂ) * b k i) = (wt r k : ℂ) • b k := rfl
  rw [this, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (wt_pos r k)]

lemma wt_le_mul_sobW (r : ℕ) (k : Mode) :
    wt r k = wt (r + 2) k * TorusFourierNS.sobW (-2) k := by
  change bse k ^ r = bse k ^ (r + 2) * bse k ^ (-2 : ℝ)
  rw [Real.rpow_neg (bse_pos k).le, pow_add]
  norm_cast
  have := (bse_pos k).ne'
  field_simp

/-- Summability of the weight-`r` embedding from an `H^{2(r+2)}` bound. -/
lemma summable_emb_of_hs {r : ℕ} {b : FField} {M : ℝ}
    (hm : TorusFourierNS.MemHsField (2 * ((r + 2 : ℕ) : ℝ)) b)
    (hn : TorusFourierNS.hsNormField (2 * ((r + 2 : ℕ) : ℝ)) b ≤ M) :
    Summable (fun k => ‖fun i => (wt r k : ℂ) * b k i‖) :=
  ((TorusFourierNS.summable_sobW_neg (s := 2) (by norm_num)).mul_left M).of_nonneg_of_le
    (fun _ => norm_nonneg _) fun k => by
      rw [norm_wt_fun, wt_le_mul_sobW, mul_right_comm]
      exact mul_le_mul_of_nonneg_right (wt_mul_norm_le hm hn k)
        (TorusFourierNS.sobW_pos _ k).le

lemma norm_emb_apply_le {r : ℕ} {b : FField} {M : ℝ}
    (hm : TorusFourierNS.MemHsField (2 * ((r + 2 : ℕ) : ℝ)) b)
    (hn : TorusFourierNS.hsNormField (2 * ((r + 2 : ℕ) : ℝ)) b ≤ M) (k : Mode) :
    ‖emb r b k‖ ≤ M * TorusFourierNS.sobW (-2) k := by
  have he : (emb r b : Mode → Fin 3 → ℂ) k = fun i => (wt r k : ℂ) * b k i :=
    funext (emb_apply (summable_emb_of_hs hm hn) k)
  rw [he]
  rw [norm_wt_fun, wt_le_mul_sobW, mul_right_comm]
  exact mul_le_mul_of_nonneg_right (wt_mul_norm_le hm hn k) (TorusFourierNS.sobW_pos _ k).le


/-- Evaluation at one coordinate, as a continuous linear map (coined). -/
def evk (k : Mode) (i : Fin 3) : CoefL1 →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun x => x k i
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl } 1 fun x => by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
    exact (norm_le_pi_norm (x k) i).trans (norm_apply_le_coefL1 x k)

@[simp] lemma evk_apply (k : Mode) (i : Fin 3) (x : CoefL1) : evk k i x = x k i := rfl

/-- Hypotheses on a coefficient curve used below (coined). -/
structure CurveHyp (ν T : ℝ) (a : ℝ → FField) : Prop where
  bound : ∀ s' : ℝ, ∃ M' : ℝ, ∀ t ∈ Icc 0 T, TorusFourierNS.MemHsField s' (a t) ∧
    TorusFourierNS.hsNormField s' (a t) ≤ M'
  integral : ∀ t ∈ Icc 0 T, ∀ k i, a t k i = a 0 k i + ∫ τ in (0 : ℝ)..t, fourierNSField ν (a τ) k i
  modeCont : ∀ k i, ContinuousOn (fun t => a t k i) (Icc 0 T)

/-- The weighted coefficient curve (coined). -/
def coefCurve (r : ℕ) (a : ℝ → FField) (t : ℝ) : CoefL1 := emb r (a t)

variable {ν T : ℝ} {a : ℝ → FField}

lemma CurveHyp.summable (h : CurveHyp ν T a) (r : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Summable (fun k => ‖fun i => (wt r k : ℂ) * a t k i‖) := by
  obtain ⟨M, hM⟩ := h.bound (2 * ((r + 2 : ℕ) : ℝ))
  exact summable_emb_of_hs (hM t ht).1 (hM t ht).2

lemma CurveHyp.coefCurve_apply (h : CurveHyp ν T a) (r : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T)
    (k : Mode) : (coefCurve r a t : Mode → Fin 3 → ℂ) k = fun i => (wt r k : ℂ) * a t k i :=
  funext (emb_apply (h.summable r ht) k)

lemma CurveHyp.continuousOn (h : CurveHyp ν T a) (r : ℕ) :
    ContinuousOn (coefCurve r a) (Icc 0 T) := by
  intro t₀ ht₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  obtain ⟨M, hM⟩ := h.bound (2 * ((r + 2 : ℕ) : ℝ))
  have hb : ∀ t ∈ Icc 0 T, ∀ k, ‖(coefCurve r a t - coefCurve r a t₀ : CoefL1) k‖ ≤
      2 * (M * TorusFourierNS.sobW (-2) k) := fun t ht k => by
    rw [lp.coeFn_sub, Pi.sub_apply, two_mul]
    exact (norm_sub_le _ _).trans (add_le_add (norm_emb_apply_le (hM t ht).1 (hM t ht).2 k)
      (norm_emb_apply_le (hM t₀ ht₀).1 (hM t₀ ht₀).2 k))
  have key := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[Icc 0 T] t₀)
    (f := fun t k => ‖(coefCurve r a t - coefCurve r a t₀ : CoefL1) k‖) (g := fun _ => (0 : ℝ))
    (((TorusFourierNS.summable_sobW_neg (s := 2) (by norm_num)).mul_left M).mul_left 2)
    (fun k => by
      have hk : Tendsto (fun t => fun i => (wt r k : ℂ) * (a t k i - a t₀ k i)) (𝓝[Icc 0 T] t₀)
          (𝓝 (fun i => (wt r k : ℂ) * (a t₀ k i - a t₀ k i))) :=
        tendsto_pi_nhds.2 fun i =>
          (((h.modeCont k i t₀ ht₀).sub continuousWithinAt_const).const_mul _)
      simp only [sub_self, mul_zero] at hk
      have := hk.norm
      have hz : (fun _ : Fin 3 => (0 : ℂ)) = 0 := rfl
      rw [hz, norm_zero] at this
      show Tendsto (fun t => ‖(coefCurve r a t - coefCurve r a t₀ : CoefL1) k‖) _ (𝓝 0)
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [lp.coeFn_sub, Pi.sub_apply, h.coefCurve_apply r ht, h.coefCurve_apply r ht₀]
      congr 1; funext i; simp [mul_sub])
    (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      intro k
      rw [norm_norm]; exact hb t ht k)
  have e : ∀ t, ‖coefCurve r a t - coefCurve r a t₀‖ =
      ∑' k, ‖(coefCurve r a t - coefCurve r a t₀ : CoefL1) k‖ := fun t => norm_coefL1 _
  simp only [e]
  simpa using key


/-- The weighted NS vector field along the curve (coined). -/
def coefField (ν : ℝ) (r : ℕ) (a : ℝ → FField) (t : ℝ) : CoefL1 :=
  nsOp ν r (coefCurve (r + 2) a t)

lemma CurveHyp.coefField_apply (h : CurveHyp ν T a) (r : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T)
    (k : Mode) (i : Fin 3) : coefField ν r a t k i = wt r k * fourierNSField ν (a t) k i :=
  nsOp_emb_coord (h.summable (r + 2) ht) k i

lemma CurveHyp.continuousOn_field (h : CurveHyp ν T a) (r : ℕ) :
    ContinuousOn (coefField ν r a) (Icc 0 T) :=
  (contDiff_nsOp (ν := ν) (r := r)).continuous.comp_continuousOn (h.continuousOn (r + 2))

/-- **Proved.** The weighted curve is differentiable within `[0,T]` with derivative the
weighted NS field. -/
theorem CurveHyp.hasDerivWithinAt (h : CurveHyp ν T a) (hT : 0 ≤ T) (r : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (coefCurve r a) (coefField ν r a t) (Icc 0 T) t := by
  set Gc : ℝ → CoefL1 := fun τ => coefField ν r a (cl T τ)
  have hGc : Continuous Gc :=
    (h.continuousOn_field r).comp_continuous (continuous_cl T) (cl_mem hT)
  have hsub : ∀ {t}, t ∈ Icc 0 T → uIcc 0 t ⊆ Icc 0 T := fun {t} ht => by
    rw [uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2
  have hrep : EqOn (coefCurve r a) (fun t => coefCurve r a 0 + ∫ τ in (0 : ℝ)..t, Gc τ)
      (Icc 0 T) := fun t ht => by
    have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
    refine lp.ext (funext fun k => funext fun i => ?_)
    rw [lp.coeFn_add, Pi.add_apply, Pi.add_apply]
    have hev := (evk k i).intervalIntegral_comp_comm
      (hGc.intervalIntegrable (μ := volume) 0 t)
    simp only [evk_apply] at hev
    rw [← hev, h.coefCurve_apply r ht, h.coefCurve_apply r h0]
    simp only
    rw [intervalIntegral.integral_congr (g := fun τ => (wt r k : ℂ) *
      fourierNSField ν (a τ) k i) (fun τ hτ => by
        simp only [Gc]
        rw [h.coefField_apply r (cl_mem hT τ), cl_of_mem (hsub ht hτ)]),
      h.integral t ht k i, mul_add]
    erw [intervalIntegral.integral_const_mul]
    rfl
  have hd : HasDerivAt (fun t => coefCurve r a 0 + ∫ τ in (0 : ℝ)..t, Gc τ) (Gc t) t :=
    (intervalIntegral.integral_hasDerivAt_right (hGc.intervalIntegrable 0 t)
      (hGc.stronglyMeasurableAtFilter _ _) hGc.continuousAt).const_add _
  have hGt : Gc t = coefField ν r a t := by simp only [Gc, cl_of_mem ht]
  rw [← hGt]
  exact hd.hasDerivWithinAt.congr hrep (hrep ht)

/-- **Proved.** The weighted curve is `C^∞` on `[0,T]`, for every weight. -/
theorem CurveHyp.contDiffOn (h : CurveHyp ν T a) (hT : 0 < T) :
    ∀ (n : ℕ) (r : ℕ), ContDiffOn ℝ n (coefCurve r a) (Icc 0 T) := by
  intro n
  induction n with
  | zero => intro r; exact contDiffOn_zero.2 (h.continuousOn r)
  | succ n ih =>
    intro r
    have hu := uniqueDiffOn_Icc hT
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by norm_cast,
      contDiffOn_succ_iff_derivWithin hu]
    refine ⟨fun t ht => (h.hasDerivWithinAt hT.le r ht).differentiableWithinAt,
      by simp, ?_⟩
    have hG : ContDiffOn ℝ n (coefField ν r a) (Icc 0 T) :=
      (contDiff_nsOp (ν := ν) (r := r)).of_le le_top |>.comp_contDiffOn (ih (r + 2))
    refine hG.congr fun t ht => ?_
    exact (h.hasDerivWithinAt hT.le r ht).derivWithin (hu t ht)

theorem CurveHyp.contDiffOn_infty (h : CurveHyp ν T a) (hT : 0 < T) (r : ℕ) :
    ContDiffOn ℝ ∞ (coefCurve r a) (Icc 0 T) :=
  _root_.contDiffOn_infty.2 fun n => h.contDiffOn hT n r

end PeriodicNSContinuation
