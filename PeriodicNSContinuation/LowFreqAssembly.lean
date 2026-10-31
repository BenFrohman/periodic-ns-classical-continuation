/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.VPKernel

/-!
# Assembly of `PeriodicLowFreqVorticityBound` (step 4)

Two-stage multiplier bound (dyadic block, then de la Vallée Poussin), `O(log R)` blocks, and
the Fourier-side Biot–Savart law. All names coined (see README).
-/

noncomputable section
open MeasureTheory Set Real FeffermanClayNS NavierStokes3D TorusFourierNS

namespace PeriodicNSContinuation

lemma charE_mul_charE (k l : Mode) (x : Fin 3 → ℝ) : charE k x * charE l x = charE (k + l) x := by
  simp only [charE, ← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply, Int.cast_add, Complex.ofReal_add, add_mul, Finset.sum_add_distrib]
  ring

lemma exp_neg_eq_charE (n : Mode) (y : Fin 3 → ℝ) :
    Complex.exp (-(2 * Real.pi * Complex.I) * ∑ j, ((n j : ℝ) : ℂ) * (y j : ℂ)) = charE (-n) y := by
  simp only [charE, Pi.neg_apply, Int.cast_neg, Complex.ofReal_neg, neg_mul, Finset.sum_neg_distrib,
    mul_neg]

/-- **Proved.** Fourier coefficients of a trigonometric polynomial. -/
lemma cubeCoeff_trig (S : Finset Mode) (d : Mode → ℂ) (n : Mode) :
    cubeCoeff (fun y => ∑ k ∈ S, d k * charE k y) n = if n ∈ S then d n else 0 := by
  unfold cubeCoeff
  simp_rw [exp_neg_eq_charE, Finset.sum_mul]
  have hi : ∀ k ∈ S, Integrable (fun y => d k * charE k y * charE (-n) y)
      ((volume : Measure (Fin 3 → ℝ)).restrict (Icc 0 1)) := fun k _ =>
    ((continuous_const.mul (continuous_charE k)).mul
      (continuous_charE (-n))).continuousOn.integrableOn_compact isCompact_Icc
  rw [integral_finset_sum S hi]
  have e : ∀ k, ∫ y in Icc (0 : Fin 3 → ℝ) 1, d k * charE k y * charE (-n) y =
      if n = k then d k else 0 := by
    intro k
    simp_rw [mul_assoc, charE_mul_charE]
    refine (MeasureTheory.integral_const_mul (d k) (charE (k + -n))).trans ?_
    erw [integral_charE]
    by_cases h : n = k
    · subst h; simp
    · rw [if_neg (fun h' => h (add_neg_eq_zero.1 h').symm), if_neg h, mul_zero]
  simp_rw [e]
  rw [Finset.sum_ite_eq]

/-- **Proved.** Crude `L¹` bound of a kernel by the `ℓ¹` norm of its coefficients. -/
lemma integral_norm_multKernel_le_sum (S : Finset Mode) (c : Mode → ℂ) (x : Fin 3 → ℝ) :
    ∫ y in Icc (0 : Fin 3 → ℝ) 1, ‖multKernel S c (x - y)‖ ≤ ∑ k ∈ S, ‖c k‖ := by
  have hK : Continuous fun y => multKernel S c (x - y) :=
    (continuous_multKernel S c).comp (continuous_const.sub continuous_id)
  calc ∫ y in Icc (0 : Fin 3 → ℝ) 1, ‖multKernel S c (x - y)‖
      ≤ ∫ _ in Icc (0 : Fin 3 → ℝ) 1, ∑ k ∈ S, ‖c k‖ :=
        setIntegral_mono_on (hK.norm.continuousOn.integrableOn_compact isCompact_Icc)
          (continuousOn_const.integrableOn_compact isCompact_Icc) measurableSet_Icc fun y _ => by
            refine (norm_sum_le _ _).trans (le_of_eq ?_)
            simp [norm_charE]
    _ = ∑ k ∈ S, ‖c k‖ := by
        rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Icc_pi_toReal (by simp)]
        simp

/-- **Proved.** Two-stage multiplier bound: a `BoxSupp M` multiplier `m` with kernel `L¹ ≤ L`,
followed by a multiplier `w` on `T` with kernel `L¹ ≤ V` at `x`. -/
theorem norm_two_stage_le {g : (Fin 3 → ℝ) → ℂ} (hg : Continuous g) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ y ∈ Icc (0 : Fin 3 → ℝ) 1, ‖g y‖ ≤ B) {M : ℕ} {m : Mode → ℂ} (hm : BoxSupp M m)
    {L : ℝ} (hL : ∀ z, ∫ y in Icc (0 : Fin 3 → ℝ) 1, ‖multKernel (modeBox M) m (z - y)‖ ≤ L)
    (T : Finset Mode) (w : Mode → ℂ) (x : Fin 3 → ℝ) {V : ℝ}
    (hV : ∫ y in Icc (0 : Fin 3 → ℝ) 1, ‖multKernel T w (x - y)‖ ≤ V) :
    ‖∑ k ∈ T, w k * (m k * cubeCoeff g k) * charE k x‖ ≤ B * L * V := by
  set G : (Fin 3 → ℝ) → ℂ := fun y => ∑ k ∈ modeBox M, (m k * cubeCoeff g k) * charE k y
  have hGc : Continuous G := continuous_finset_sum _ fun k _ => continuous_const.mul (continuous_charE k)
  have hGB : ∀ y ∈ Icc (0 : Fin 3 → ℝ) 1, ‖G y‖ ≤ B * L := fun y _ => by
    have := norm_multiplier_le hg hB (modeBox M) m y
    exact this.trans (mul_le_mul_of_nonneg_left (hL y) hB0)
  have hcoef : ∀ k, m k * cubeCoeff g k = cubeCoeff G k := by
    intro k
    rw [cubeCoeff_trig]
    split_ifs with h
    · rfl
    · rw [hm k h, zero_mul]
  have hBL : 0 ≤ B * L := (norm_nonneg _).trans (hGB 0 ⟨le_rfl, zero_le_one⟩)
  simp_rw [hcoef]
  exact (norm_multiplier_le hGc hGB T w x).trans (mul_le_mul_of_nonneg_left hV hBL)


/-- Coined. Riesz-type symbol `k_j k_b / |k|²` (`= 0` at `k = 0`). -/
def qC (j b : Fin 3) (k : Mode) : ℂ := ((modeR k j * modeR k b / sqn (modeR k) : ℝ) : ℂ)

/-- Coined. Low-frequency piece `q · χ(|k|²)` of `qC`. -/
def qLow (j b : Fin 3) (k : Mode) : ℂ :=
  ((modeR k j * modeR k b / sqn (modeR k) * cutχ (sqn (modeR k)) : ℝ) : ℂ)

lemma qC_split (j b : Fin 3) {S : ℕ} {k : Mode} (hk : sqn (modeR k) ≤ 4 ^ S) :
    qC j b k = qLow j b k + ∑ s ∈ Finset.range S, blockC j b s k := by
  rw [sum_blockC, cutχ_one ((div_le_one (by positivity)).2 hk), qC, qLow]
  push_cast; ring

lemma boxSupp_qLow (j b : Fin 3) : BoxSupp 1 (qLow j b) := by
  intro k hk
  rw [mem_modeBox] at hk; push Not at hk
  obtain ⟨i, hi⟩ := hk
  have h2 : (2 : ℤ) ≤ |k i| := by simpa using hi
  have h4 : (4 : ℝ) ≤ modeR k i ^ 2 := by
    have : (2 : ℝ) ≤ |(k i : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast h2
    show (4 : ℝ) ≤ (k i : ℝ) ^ 2
    nlinarith [sq_abs (k i : ℝ), abs_nonneg (k i : ℝ)]
  have : 2 ≤ sqn (modeR k) := by linarith [sq_le_sqn (modeR k) i]
  simp [qLow, cutχ_zero this]

lemma sqn_le_of_mem {N : ℕ} {k : Mode} (hk : k ∈ modeBox N) : sqn (modeR k) ≤ 3 * (N : ℝ) ^ 2 := by
  rw [mem_modeBox] at hk
  have h : ∀ i, modeR k i ^ 2 ≤ (N : ℝ) ^ 2 := fun i => by
    have : |(k i : ℝ)| ≤ N := by rw [← Int.cast_abs]; exact_mod_cast hk i
    simpa [modeR, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) this 2
  simp only [sqn, Fin.sum_univ_three]; linarith [h 0, h 1, h 2]

/-- **Proved.** The composite multiplier `vpWeight · k_j k_b/|k|²` maps `L^∞ → L^∞` with norm
`O(1 + log R)`. -/
theorem exists_qvp_bound (j b : Fin 3) : ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 2 ≤ R →
    ∀ g : (Fin 3 → ℝ) → ℂ, Continuous g → ∀ B : ℝ, 0 ≤ B →
    (∀ y ∈ Icc (0 : Fin 3 → ℝ) 1, ‖g y‖ ≤ B) → ∀ x : Fin 3 → ℝ,
    ‖∑ k ∈ modeBox ⌈2 * R⌉₊, ((vpWeight R k : ℝ) : ℂ) * (qC j b k * cubeCoeff g k) * charE k x‖ ≤
      C * (1 + Real.log R) * B := by
  obtain ⟨Cv, hCv0, hCv⟩ := exists_vp_L1_bound
  obtain ⟨Cb, hCb0, hCb⟩ := exists_blockC_L1_bound j b
  set L0 := ∑ k ∈ modeBox 1, ‖qLow j b k‖
  have hL0 : 0 ≤ L0 := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨Cv * (L0 + 4 * Cb), by positivity, fun R hR g hg B hB0 hB x => ?_⟩
  have hR0 : 0 < R := by linarith
  set N := ⌈2 * R⌉₊
  set S := ⌈Real.logb 2 R⌉₊ + 3
  have hlogb : 0 ≤ Real.logb 2 R := Real.logb_nonneg (by norm_num) (by linarith)
  have hlog : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
  -- `2^S ≥ 8R`, hence `4^S ≥ 64 R² ≥ sqn` on the box
  have h2S : 8 * R ≤ (2 : ℝ) ^ S := by
    have h1 : R ≤ (2 : ℝ) ^ ⌈Real.logb 2 R⌉₊ := by
      rw [← Real.rpow_natCast]
      calc R = (2 : ℝ) ^ Real.logb 2 R := (Real.rpow_logb (by norm_num) (by norm_num) hR0).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
    rw [pow_add]; norm_num; linarith
  have hN : (N : ℝ) ≤ 2 * R + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hsq : ∀ k ∈ modeBox N, sqn (modeR k) ≤ 4 ^ S := fun k hk => by
    have e : (4 : ℝ) ^ S = ((2 : ℝ) ^ S) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    rw [e]
    nlinarith [sqn_le_of_mem hk, mul_le_mul hN hN hN0 (by linarith : (0 : ℝ) ≤ 2 * R + 1),
      mul_le_mul h2S h2S (by linarith) (by positivity : (0 : ℝ) ≤ 2 ^ S)]
  -- split the sum
  have hsplit : ∑ k ∈ modeBox N, ((vpWeight R k : ℝ) : ℂ) * (qC j b k * cubeCoeff g k) * charE k x =
      ∑ k ∈ modeBox N, ((vpWeight R k : ℝ) : ℂ) * (qLow j b k * cubeCoeff g k) * charE k x +
      ∑ s ∈ Finset.range S, ∑ k ∈ modeBox N,
        ((vpWeight R k : ℝ) : ℂ) * (blockC j b s k * cubeCoeff g k) * charE k x := by
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [qC_split j b (hsq k hk), add_mul, Finset.sum_mul, mul_add, Finset.mul_sum, add_mul,
      Finset.sum_mul]
  have hV := fun x => hCv R hR x
  have hlow := norm_two_stage_le hg hB0 hB (boxSupp_qLow j b)
    (fun z => integral_norm_multKernel_le_sum _ _ z) (modeBox N) _ x (hV x)
  have hblk : ∀ s ∈ Finset.range S, ‖∑ k ∈ modeBox N,
      ((vpWeight R k : ℝ) : ℂ) * (blockC j b s k * cubeCoeff g k) * charE k x‖ ≤ B * Cb * Cv :=
    fun s _ => norm_two_stage_le hg hB0 hB (boxSupp_blockC j b s) (hCb s) (modeBox N) _ x (hV x)
  have hS : (S : ℝ) ≤ 4 * (1 + Real.log R) := by
    have h1 : (⌈Real.logb 2 R⌉₊ : ℝ) ≤ Real.logb 2 R + 1 := (Nat.ceil_lt_add_one hlogb).le
    have h2 : Real.logb 2 R ≤ 2 * Real.log R := by
      rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
      nlinarith [Real.log_two_gt_d9]
    simp only [S, Nat.cast_add, Nat.cast_ofNat]; linarith
  rw [hsplit]
  calc _ ≤ ‖∑ k ∈ modeBox N, ((vpWeight R k : ℝ) : ℂ) * (qLow j b k * cubeCoeff g k) * charE k x‖ +
        ∑ s ∈ Finset.range S, ‖∑ k ∈ modeBox N,
          ((vpWeight R k : ℝ) : ℂ) * (blockC j b s k * cubeCoeff g k) * charE k x‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ B * L0 * Cv + S * (B * Cb * Cv) := by
        refine add_le_add hlow ?_
        refine (Finset.sum_le_sum hblk).trans (le_of_eq ?_)
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ Cv * (L0 + 4 * Cb) * (1 + Real.log R) * B := by
        have hX : 0 ≤ B * Cb * Cv := by positivity
        have h1 : B * L0 * Cv ≤ B * L0 * Cv * (1 + Real.log R) :=
          le_mul_of_one_le_right (by positivity) (by linarith)
        nlinarith [mul_le_mul_of_nonneg_right hS hX]


lemma vort_coord_eq (v : VelocityField) (a : Fin 3) (y : T3) :
    vorticity v y a = pdR (a + 1) (fun z => v z (a + 2)) y - pdR (a + 2) (fun z => v z (a + 1)) y := by
  fin_cases a
  · exact (vort_comp v y).1
  · exact (vort_comp v y).2.1
  · exact (vort_comp v y).2.2

lemma abs_vort_coord_le {v : VelocityField} (hv : IsPeriodicSmoothInitialData v) (a : Fin 3)
    (y : T3) : |vorticity v y a| ≤ 2 * gradSupNorm v := by
  rw [vort_coord_eq]
  have := abs_sub (pdR (a + 1) (fun z => v z (a + 2)) y) (pdR (a + 2) (fun z => v z (a + 1)) y)
  linarith [abs_pdR_coord_le hv (a + 1) (a + 2) y, abs_pdR_coord_le hv (a + 2) (a + 1) y]

/-- **Proved.** The vorticity of smooth periodic data is bounded. -/
lemma bddAbove_norm_vorticity {v : VelocityField} (hv : IsPeriodicSmoothInitialData v) :
    BddAbove (range fun y => ‖vorticity v y‖) := by
  refine ⟨Real.sqrt (3 * (2 * gradSupNorm v) ^ 2), ?_⟩
  rintro _ ⟨y, rfl⟩
  show ‖vorticity v y‖ ≤ _
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  rw [Fin.sum_univ_three]
  have h : ∀ a, ‖vorticity v y a‖ ^ 2 ≤ (2 * gradSupNorm v) ^ 2 := fun a => by
    rw [Real.norm_eq_abs, sq_abs]
    have h1 := abs_vort_coord_le hv a y
    nlinarith [abs_nonneg (vorticity v y a), sq_abs (vorticity v y a)]
  linarith [h 0, h 1, h 2]

lemma continuous_vort_coord {v : VelocityField} (hv : IsPeriodicSmoothInitialData v) (a : Fin 3) :
    Continuous (liftR fun y => vorticity v y a) := by
  have hφ : ∀ l, PerR (fun y => v y l) := fun l => perR_coord hv.1 hv.2.2 l
  have e : (fun y => vorticity v y a) =
      fun y => pdR (a + 1) (fun z => v z (a + 2)) y - pdR (a + 2) (fun z => v z (a + 1)) y :=
    funext (vort_coord_eq v a)
  rw [e]
  exact Complex.continuous_ofReal.comp
    ((((hφ _).pdR _).cont.sub ((hφ _).pdR _).cont).comp
      (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous)

lemma norm_vort_coord_le {v : VelocityField} (hv : IsPeriodicSmoothInitialData v) (a : Fin 3)
    (y : Fin 3 → ℝ) : ‖liftR (fun y => vorticity v y a) y‖ ≤ vorticity_sup_norm (vorticity v) := by
  simp only [liftR, Complex.norm_real]
  exact (PiLp.norm_apply_le _ _).trans (le_vorticity_sup_norm _ _ (bddAbove_norm_vorticity hv))

/-- **Proved.** Biot–Savart in Riesz form: `∂̂_j v_i = q_{j,i+2} ω̂_{i+1} − q_{j,i+1} ω̂_{i+2}`. -/
lemma gradCoeff_eq_qC {v : VelocityField} (hv : IsPeriodicSmoothInitialData v) (k : Mode)
    (i j : Fin 3) :
    gradCoeff v k i j = qC j (i + 2) k * vortCoeff v k (i + 1) -
      qC j (i + 1) k * vortCoeff v k (i + 2) := by
  by_cases hk : k = 0
  · subst hk; simp [gradCoeff_zero, qC, modeR]
  rw [gradCoeff_eq_vort hv hk]
  fin_cases i <;> simp [crossC, kvec, ksq, qC, modeR, sqn, Fin.sum_univ_three] <;> ring

/-- **Proved.** `PeriodicLowFreqVorticityBound`. -/
theorem periodicLowFreqVorticityBound : PeriodicLowFreqVorticityBound := by
  choose C hC0 hC using exists_qvp_bound
  set Cm := ∑ j, ∑ b, C j b
  have hCm : ∀ j b, C j b ≤ Cm := fun j b =>
    (Finset.single_le_sum (f := fun b => C j b) (fun b _ => hC0 j b) (Finset.mem_univ b)).trans
      (Finset.single_le_sum (f := fun j => ∑ b, C j b)
        (fun j _ => Finset.sum_nonneg fun b _ => hC0 j b) (Finset.mem_univ j))
  have hCm0 : 0 ≤ Cm := (hC0 0 0).trans (hCm 0 0)
  refine ⟨18 * Cm, by positivity, fun R hR v hv => ?_⟩
  have hR0 : 0 < R := by linarith
  set W := vorticity_sup_norm (vorticity v)
  have hW : 0 ≤ W := vorticity_sup_norm_nonneg _
  have hlog : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
  have hpiece : ∀ j b a (x : Fin 3 → ℝ), ‖∑ k ∈ modeBox ⌈2 * R⌉₊, ((vpWeight R k : ℝ) : ℂ) *
      (qC j b k * vortCoeff v k a) * charE k x‖ ≤ Cm * (1 + Real.log R) * W := fun j b a x =>
    (hC j b R hR _ (continuous_vort_coord hv a) W hW (fun y _ => norm_vort_coord_le hv a y) x).trans
      (by gcongr; exact hCm j b)
  have hentry : ∀ x : T3, ∀ i j, ‖lowGrad R v x i j‖ ≤ 2 * (Cm * (1 + Real.log R) * W) := by
    intro x i j
    have e : lowGrad R v x i j =
        ∑ k ∈ modeBox ⌈2 * R⌉₊, ((vpWeight R k : ℝ) : ℂ) *
          (qC j (i + 2) k * vortCoeff v k (i + 1)) * charE k (fun l => x l) -
        ∑ k ∈ modeBox ⌈2 * R⌉₊, ((vpWeight R k : ℝ) : ℂ) *
          (qC j (i + 1) k * vortCoeff v k (i + 2)) * charE k (fun l => x l) := by
      rw [← Finset.sum_sub_distrib, lowGrad, tsum_eq_sum (s := modeBox ⌈2 * R⌉₊) fun k hk => by
        have h0 := boxSupp_vp hR0 k hk
        simp only at h0
        rw [h0, zero_mul, zero_mul]]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [gradCoeff_eq_qC hv]; simp only [charE]; ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    linarith [hpiece j (i + 2) (i + 1) (fun l => x l), hpiece j (i + 1) (i + 2) (fun l => x l)]
  refine ciSup_le fun x => ?_
  calc ∑ i, ∑ j, ‖lowGrad R v x i j‖ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, 2 * (Cm * (1 + Real.log R) * W) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry x i j
    _ = 18 * Cm * (1 + Real.log R) * W := by simp; ring

end PeriodicNSContinuation
