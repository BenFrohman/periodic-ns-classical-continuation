import PeriodicNSContinuation.SeriesCalculus

/-!
# The momentum equation for the series velocity and pressure (all names coined)

Under `CurveHyp` (all `H^{s'}` bounds, the integral equation, and continuity of each mode in
time) plus Hermitian symmetry and divergence-freeness of the coefficients, the reconstructed
pressure is jointly `C^∞` and `(seriesVelocity a, seriesPressure a)` satisfy the momentum
equation on `[0,T] × T3`.
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D
open scoped ContDiff

namespace PeriodicNSContinuation

open TorusFourierNS (Mode FField)

lemma evOp_coord {r : ℕ} (hr : 2 ≤ r) (x : T3) (y : CoefL1) (i : Fin 3) {c : Mode → ℂ}
    (hy : ∀ n, (y : Mode → Fin 3 → ℂ) n i = wt r n * c n) : evOp r x y i = seriesC c x := by
  rw [evOp_apply hr]
  have hs : Summable fun n =>
      (((wt r n)⁻¹ : ℝ) * phase n x) • (y : Mode → Fin 3 → ℂ) n :=
    (summable_evTerm hr x).map (ContinuousLinearMap.apply ℝ (Fin 3 → ℂ) y)
      (ContinuousLinearMap.continuous _) |>.congr fun n => rfl
  have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℂ) i).map_tsum hs
  simp only [ContinuousLinearMap.proj_apply] at this
  rw [this]
  unfold seriesC
  refine tsum_congr fun n => ?_
  simp only [Pi.smul_apply, smul_eq_mul, hy n]
  have : (wt r n : ℂ) ≠ 0 := by exact_mod_cast (wt_pos r n).ne'
  push_cast
  field_simp

lemma hs_of_coefL1 {r p : ℕ} (hpr : p ≤ r) (y : CoefL1) (i : Fin 3) {c : Mode → ℂ}
    (hy : ∀ n, (y : Mode → Fin 3 → ℂ) n i = wt r n * c n) : HS p c :=
  (summable_norm_coefL1 y).of_nonneg_of_le (fun n => by have := bse_pos n; positivity) fun n => by
    calc ‖c n‖ * bse n ^ p ≤ ‖c n‖ * wt r n :=
          mul_le_mul_of_nonneg_left (by unfold wt; exact pow_le_pow_right₀ (one_le_bse n) hpr)
            (norm_nonneg _)
      _ = ‖(y : Mode → Fin 3 → ℂ) n i‖ := by
          rw [hy, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (wt_pos r n), mul_comm]
      _ ≤ ‖(y : Mode → Fin 3 → ℂ) n‖ := norm_le_pi_norm _ i

variable {ν T : ℝ} {a : ℝ → FField}

lemma CurveHyp.bil_coord (h : CurveHyp ν T a) (r : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) (k : Mode)
    (j : Fin 3) : (bilOp r (coefCurve (r + 2) a t) (coefCurve (r + 2) a t) : Mode → Fin 3 → ℂ) k j =
      wt r k * nonlinCoeff (a t) k j := by
  have := congrFun (bilRaw_emb (h.summable (r + 2) ht) k) j
  rw [Pi.smul_apply, Complex.real_smul] at this
  exact this

lemma CurveHyp.hs_nonlin (h : CurveHyp ν T a) (p : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) (j : Fin 3) :
    HS p (fun k => nonlinCoeff (a t) k j) :=
  hs_of_coefL1 le_rfl _ j fun k => h.bil_coord p ht k j

lemma CurveHyp.hs_press (h : CurveHyp ν T a) (p : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HS p (fun k => pressureCoeff k (nonlinCoeff (a t) k)) :=
  hs_of_coefL1 le_rfl _ 0 fun k => pressOp_bil_emb (h.summable (p + 2) ht) k 0

lemma seriesPressure_eq_evOp (h : CurveHyp ν T a) {r : ℕ} (hr : 2 ≤ r) {t : ℝ}
    (ht : t ∈ Icc 0 T) (x : T3) :
    seriesPressure a t x =
      reVec (evOp r x (pressOp (bilOp r (coefCurve (r + 2) a t) (coefCurve (r + 2) a t)))) 0 := by
  rw [reVec_apply, evOp_coord hr x
    (pressOp (bilOp r (coefCurve (r + 2) a t) (coefCurve (r + 2) a t))) 0
    (c := fun k => pressureCoeff k (nonlinCoeff (a t) k))
    (fun n => pressOp_bil_emb (h.summable (r + 2) ht) n 0)]
  rfl

/-- **Proved.** Joint `C^∞` regularity of the series pressure on `[0,T] × T3`, under `CurveHyp`. -/
theorem CurveHyp.contDiffOn_seriesPressure (h : CurveHyp ν T a) (hT : 0 < T) :
    ContDiffOn ℝ ∞ (fun q : ℝ × T3 => seriesPressure a q.1 q.2) (Icc (0 : ℝ) T ×ˢ univ) := by
  refine _root_.contDiffOn_infty.2 fun N => ?_
  have hE : ContDiffOn ℝ N (fun q : ℝ × T3 => evOp (N + 2) q.2) (Icc (0 : ℝ) T ×ˢ univ) :=
    ((contDiff_evOp le_rfl).comp contDiff_snd).contDiffOn
  have hP : ContDiff ℝ ⊤ (fun X : CoefL1 => pressOp (bilOp (N + 2) X X)) :=
    pressOp.contDiff.comp ((bilOp (N + 2)).contDiff.clm_apply contDiff_id)
  have hc : ContDiffOn ℝ N (fun q : ℝ × T3 => pressOp (bilOp (N + 2)
      (coefCurve (N + 2 + 2) a q.1) (coefCurve (N + 2 + 2) a q.1))) (Icc (0 : ℝ) T ×ˢ univ) :=
    (hP.of_le le_top).comp_contDiffOn
      ((h.contDiffOn hT N (N + 2 + 2)).comp contDiff_fst.contDiffOn fun q hq => hq.1)
  refine ((EuclideanSpace.proj (0 : Fin 3)).contDiff.comp_contDiffOn
    (reVec.contDiff.comp_contDiffOn (hE.clm_apply hc))).congr fun q hq => ?_
  exact seriesPressure_eq_evOp h (by omega) hq.1 q.2

lemma CurveHyp.hasDerivWithinAt_seriesVelocity (h : CurveHyp ν T a) (hT : 0 ≤ T) {t : ℝ}
    (ht : t ∈ Icc 0 T) (x : T3) :
    HasDerivWithinAt (fun s => seriesVelocity a s x)
      (reVec (evOp 2 x (coefField ν 2 a t))) (Icc 0 T) t := by
  have := ((reVec.comp (evOp 2 x)).hasFDerivAt).comp_hasDerivWithinAt t
    (h.hasDerivWithinAt hT 2 ht)
  exact this.congr (fun s hs => seriesVelocity_eq_evOp h le_rfl hs x)
    (seriesVelocity_eq_evOp h le_rfl ht x)

/-- **Proved.** The momentum equation for the reconstructed velocity and pressure, under
`CurveHyp` plus Hermitian symmetry of the coefficients. -/
theorem CurveHyp.momentum (h : CurveHyp ν T a) (hT : 0 < T)
    (hH : ∀ t ∈ Icc 0 T, TorusFourierNS.HermitianField (a t)) {t : ℝ} (ht : t ∈ Icc 0 T)
    (x : T3) :
    derivWithin (fun s => seriesVelocity a s x) (Icc (0 : ℝ) T) t +
        convective (seriesVelocity a t) (seriesVelocity a t) x =
      ν • laplacian (seriesVelocity a t) x - pressureGradient (seriesPressure a t) x +
        (fun _ _ => (0 : EuclideanSpace ℝ (Fin 3))) t x := by
  have hb : ∀ p j, HS p (fun n => a t n j) := fun p j => AllHsBound.hs h.bound ht p j
  rw [(h.hasDerivWithinAt_seriesVelocity hT.le ht x).derivWithin (uniqueDiffOn_Icc hT t ht)]
  have hconv : convective (seriesVelocity a t) (seriesVelocity a t) x =
      vecS (fun j n => a t n j * lin n (vecS (fun l n => a t n l) x)) x := by
    unfold convective
    rw [seriesVelocity_eq_vecS, fderiv_vecS_apply fun j => hb 1 j]
  have hlap := laplacian_vecS (c := fun j n => a t n j) (fun j => hb 3 j) x
  rw [hconv, seriesVelocity_eq_vecS, hlap]
  ext i
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, vecS_apply,
    add_zero]
  have hp : seriesPressure a t = fun y =>
      (seriesC (fun k => pressureCoeff k (nonlinCoeff (a t) k)) y).re := rfl
  rw [hp, gradient_re_seriesC (h.hs_press 1 ht) x i, reVec_apply,
    evOp_coord le_rfl _ _ i (c := fun k => fourierNSField ν (a t) k i)
      (fun n => h.coefField_apply 2 ht n i),
    seriesC_convective (hH t ht) (fun j => hb 1 j) x i]
  -- complex identity
  set L : Mode → ℂ := fun n =>
    -((4 * Real.pi ^ 2 * TorusFourierNS.ksq (TorusFourierNS.kvec n) : ℝ) : ℂ) * a t n i
  set Nc : Mode → ℂ := fun k => nonlinCoeff (a t) k i
  set G : Mode → ℂ := fun n => 2 * Real.pi * Complex.I * ((n i : ℝ) : ℂ) *
    pressureCoeff n (nonlinCoeff (a t) n)
  have hL : HS 0 L := ((hb 1 i).mul_left (4 * Real.pi ^ 2)).of_nonneg_of_le
      (fun n => by positivity) fun n => by
    simp only [L, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, pow_zero, mul_one,
      pow_one]
    rw [abs_of_nonneg (sq_nonneg Real.pi), abs_of_nonneg (ksq_nonneg' n)]
    have h1 := mul_le_mul_of_nonneg_right (ksq_le_bse n) (norm_nonneg (a t n i))
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 4 * Real.pi ^ 2)
    try rw [abs_of_pos (by norm_num : (0:ℝ) < 4)]
    exact le_trans (le_of_eq (by ring)) (h2.trans (le_of_eq (by ring)))
  have hN : HS 0 Nc := h.hs_nonlin 0 ht i
  have hG : HS 0 G := by
    have h1 : HS 0 (fun n => ((n i : ℝ) : ℂ) * pressureCoeff n (nonlinCoeff (a t) n)) :=
      (summable_norm_int_mul (h.hs_press 1 ht) i).congr fun n => by simp
    exact (h1.const_mul (2 * Real.pi * Complex.I)).congr fun n => by simp only [G]; ring_nf
  have e : (fun k => fourierNSField ν (a t) k i) =
      (fun n => (ν : ℂ) * L n) + ((fun n => (-1 : ℂ) * Nc n) + fun n => (-1 : ℂ) * G n) := by
    funext n
    simp only [Pi.add_apply, L, Nc, G]
    rw [fourierNSField_eq_pressure]
    unfold TorusFourierNS.viscCoeff TorusFourierNS.kvec
    push_cast
    ring
  have hC : seriesC (fun k => fourierNSField ν (a t) k i) x =
      ν * seriesC L x - seriesC Nc x - seriesC G x := by
    rw [e, seriesC_add (hL.const_mul _) ((hN.const_mul _).add (hG.const_mul _)),
      seriesC_add (hN.const_mul _) (hG.const_mul _)]
    simp only [seriesC_const_mul]
    ring
  rw [hC]
  simp only [Complex.sub_re, Complex.re_ofReal_mul]
  ring

end PeriodicNSContinuation
