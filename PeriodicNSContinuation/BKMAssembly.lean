/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.BKMLog

/-!
# Assembly of the log-Sobolev BKM bound (names coined)

`periodicLogSobolevBKMBound_of_lowFreq`: for `s > 5/2`,
`PeriodicLowFreqVorticityBound → PeriodicLogSobolevBKMBound s`. **Proved**; the only input is
that one Prop.
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D TorusFourierNS

namespace PeriodicNSContinuation

/-- Coined. Unit vector `e_j` in `T3`. -/
abbrev ev (j : Fin 3) : T3 := EuclideanSpace.single j (1 : ℝ)

lemma phase_shift (k : Mode) (x : T3) (j : Fin 3) (t : ℝ) :
    phase k (x + t • ev j) = phase k x * Complex.exp (2 * Real.pi * Complex.I * (k j : ℂ) * (t : ℂ)) := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  have : ∀ l, ((k l : ℝ) : ℂ) * (((x + t • ev j) l : ℝ) : ℂ) =
      ((k l : ℝ) : ℂ) * ((x l : ℝ) : ℂ) + (if l = j then ((k j : ℝ) : ℂ) * t else 0) := fun l => by
    by_cases h : l = j
    · subst h; simp [ev]; ring
    · simp [ev, h]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  push_cast; ring

/-- Coined. `|k_j| ‖v̂_{k,i}‖` is summable for smooth periodic data. -/
lemma summable_mode_mul_coeff {v : VelocityField} (hu : IsPeriodicSmoothInitialData v)
    (i j : Fin 3) : Summable fun k : Mode => |(k j : ℝ)| * ‖fourierCoeffVF v k i‖ := by
  have hH := periodicDataHs 3 v hu
  unfold TorusFourierNS.MemHsField at hH
  have hHi : Summable fun k : Mode => sobW 3 k * ‖fourierCoeffVF v k i‖ ^ 2 :=
    hH.comp_injective (i := fun k => (k, i)) fun a b h => by simpa using h
  have hneg := summable_sobW_neg (s := 2) (by norm_num)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun k => ?_) (hneg.add hHi)
  have hp := one_add_sq_pos k
  have hA : 0 < sobW 2 k := Real.rpow_pos_of_pos hp _
  have hinv : sobW (-2) k = (sobW 2 k)⁻¹ := Real.rpow_neg hp.le _
  have hkj : ((k j : ℝ)) ^ 2 ≤ 1 + ∑ l, ((k l : ℝ)) ^ 2 := by
    have := Finset.single_le_sum (f := fun l => ((k l : ℝ)) ^ 2) (fun l _ => sq_nonneg _)
      (Finset.mem_univ j)
    linarith
  have h3 : sobW 2 k * ((k j : ℝ)) ^ 2 ≤ sobW 3 k := by
    unfold sobW
    rw [show (3:ℝ) = 2 + 1 by norm_num, Real.rpow_add hp, Real.rpow_one]
    exact mul_le_mul_of_nonneg_left hkj (Real.rpow_nonneg hp.le _)
  have := norm_le_aux (c := |(k j : ℝ)| * ‖fourierCoeffVF v k i‖) (by positivity) hA
  rw [hinv]
  refine this.trans (add_le_add le_rfl ?_)
  rw [mul_pow, sq_abs, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h3 (sq_nonneg _)

lemma norm_gradCoeff (v : VelocityField) (k : Mode) (i j : Fin 3) :
    ‖gradCoeff v k i j‖ = 2 * Real.pi * (|(k j : ℝ)| * ‖fourierCoeffVF v k i‖) := by
  simp [gradCoeff, Complex.norm_real, abs_of_pos Real.pi_pos]
  ring

/-- **Proved.** Termwise-differentiated Fourier inversion:
`∂_j v_i(x) = ∑_k 2πi k_j v̂_{k,i} e^{2πik·x}`. -/
theorem hasSum_grad {v : VelocityField} (hu : IsPeriodicSmoothInitialData v) (i j : Fin 3)
    (x : T3) : HasSum (fun k => gradCoeff v k i j * phase k x)
      (((fderiv ℝ v x (ev j)) i : ℝ) : ℂ) := by
  set g : Mode → ℝ → ℂ := fun k t => fourierCoeffVF v k i * phase k (x + t • ev j)
  set g' : Mode → ℝ → ℂ := fun k t =>
    gradCoeff v k i j * phase k (x + t • ev j)
  have hg : ∀ k t, HasDerivAt (g k) (g' k t) t := fun k t => by
    have e : g k = fun t : ℝ => fourierCoeffVF v k i * phase k x *
        Complex.exp (2 * Real.pi * Complex.I * (k j : ℂ) * (t : ℂ)) := by
      funext t; simp only [g, phase_shift]; ring
    rw [e]
    have h1 : HasDerivAt (fun t : ℝ => 2 * Real.pi * Complex.I * (k j : ℂ) * (t : ℂ))
        (2 * Real.pi * Complex.I * (k j : ℂ) * 1) t :=
      (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul _
    have := (h1.cexp).const_mul (fourierCoeffVF v k i * phase k x)
    convert this using 1
    simp only [g', gradCoeff, phase_shift]; ring
  set u : Mode → ℝ := fun k => 2 * Real.pi * (|(k j : ℝ)| * ‖fourierCoeffVF v k i‖)
  have hus : Summable u := (summable_mode_mul_coeff hu i j).mul_left _
  have hb : ∀ k t, ‖g' k t‖ ≤ u k := fun k t => by
    simp [g', norm_phase, norm_gradCoeff, u]
  have hg0 : Summable fun k => g k 0 := by
    refine Summable.of_norm_bounded (summable_norm_fourierCoeffVF hu i) fun k => ?_
    simp [g, norm_phase]
  have hD := hasDerivAt_tsum hus hg hb hg0 0
  have hfun : (fun t => ∑' k, g k t) = fun t => ((v (x + t • ev j) i : ℝ) : ℂ) := by
    funext t; exact (fourierCoeffVF_hasSum hu i (x + t • ev j)).tsum_eq
  rw [hfun] at hD
  have hdiff : DifferentiableAt ℝ v x := (hu.1.differentiable (by simp)).differentiableAt
  have hline : HasDerivAt (fun t : ℝ => x + t • ev j) (ev j) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (ev j)).const_add x
  have hv : HasDerivAt (fun t : ℝ => v (x + t • ev j)) (fderiv ℝ v x (ev j)) 0 :=
    hdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hvi : HasDerivAt (fun t : ℝ => v (x + t • ev j) i) (fderiv ℝ v x (ev j) i) 0 := by
    have := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt (0:ℝ) hv
    simpa using this
  have hc := hvi.ofReal_comp
  have heq := hD.unique hc
  have hs : Summable fun k => g' k 0 := Summable.of_norm_bounded hus (fun k => hb k 0)
  have := hs.hasSum
  simp only [g', zero_smul, add_zero] at this heq
  rwa [heq] at this

lemma abs_le_of_modeSq_le {R : ℝ} (hR : 0 < R) {k : Mode} (h : modeSq k ≤ R ^ 2) (l : Fin 3) :
    |(k l : ℝ)| ≤ R := by
  have : ((k l : ℝ)) ^ 2 ≤ R ^ 2 := le_trans (Finset.single_le_sum
    (f := fun l => ((k l : ℝ)) ^ 2) (fun l _ => sq_nonneg _) (Finset.mem_univ l)) h
  simpa [abs_of_pos hR] using sq_le_sq.mp this

lemma lowGrad_eq (R : ℝ) (v : VelocityField) (x : T3) (i j : Fin 3) :
    lowGrad R v x i j = ∑' k, (vpWeight R k : ℂ) * (gradCoeff v k i j * phase k x) := by
  unfold lowGrad phase; simp only [mul_assoc]

/-- **Proved.** Entry bound: `|∂_j v_i(x)| ≤ |V_R ∂_j v_i(x)| + 2π ∑_{|k|>R} |k_j| |v̂_{k,i}|`. -/
theorem entry_le {v : VelocityField} (hu : IsPeriodicSmoothInitialData v) {R : ℝ} (hR : 0 < R)
    (i j : Fin 3) (x : T3) :
    |(fderiv ℝ v x (ev j)) i| ≤ ‖lowGrad R v x i j‖ + 2 * Real.pi *
      ∑' k : Mode, (if modeSq k ≤ R ^ 2 then 0 else |(k j : ℝ)| * ‖fourierCoeffVF v k i‖) := by
  set a := fun k => gradCoeff v k i j * phase k x
  have hna : ∀ k, ‖a k‖ = 2 * Real.pi * (|(k j : ℝ)| * ‖fourierCoeffVF v k i‖) := fun k => by
    simp [a, norm_phase, norm_gradCoeff]
  have hsn : Summable fun k => ‖a k‖ := by
    simp only [hna]; exact (summable_mode_mul_coeff hu i j).mul_left _
  have hvp := vpWeight_nonneg R; have hvp1 := vpWeight_le_one R
  have h1 : Summable fun k => (vpWeight R k : ℂ) * a k :=
    Summable.of_norm_bounded hsn fun k => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hvp k)]
      exact mul_le_of_le_one_left (norm_nonneg _) (hvp1 k)
  have hb2 : ∀ k, ‖(1 - (vpWeight R k : ℂ)) * a k‖ ≤ 2 * Real.pi *
      (if modeSq k ≤ R ^ 2 then 0 else |(k j : ℝ)| * ‖fourierCoeffVF v k i‖) := fun k => by
    have e : (1 - (vpWeight R k : ℂ)) = ((1 - vpWeight R k : ℝ) : ℂ) := by push_cast; ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hvp1 k]),
      hna]
    split_ifs with h
    · rw [vpWeight_eq_one hR (abs_le_of_modeSq_le hR h)]; simp
    · have := hvp k
      have : 0 ≤ 2 * Real.pi * (|(k j : ℝ)| * ‖fourierCoeffVF v k i‖) := by positivity
      nlinarith
  have hind : Summable fun k : Mode => 2 * Real.pi *
      (if modeSq k ≤ R ^ 2 then 0 else |(k j : ℝ)| * ‖fourierCoeffVF v k i‖) :=
    Summable.mul_left _ (Summable.of_nonneg_of_le (fun k => by split_ifs <;> positivity)
      (fun k => by split_ifs <;> simp [mul_nonneg]) (summable_mode_mul_coeff hu i j))
  have h2 : Summable fun k => ‖(1 - (vpWeight R k : ℂ)) * a k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb2 hind
  have hsplit : (((fderiv ℝ v x (ev j)) i : ℝ) : ℂ) =
      lowGrad R v x i j + ∑' k, (1 - (vpWeight R k : ℂ)) * a k := by
    rw [← (hasSum_grad hu i j x).tsum_eq, lowGrad_eq, ← h1.tsum_add h2.of_norm]
    congr 1; funext k; ring
  have := congrArg norm hsplit
  rw [Complex.norm_real, Real.norm_eq_abs] at this
  rw [this, ← tsum_mul_left]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  exact (norm_tsum_le_tsum_norm h2).trans (h2.tsum_le_tsum hb2 hind)

/-- **Proved.** `‖L‖ ≤ ∑_j ∑_i |L e_j · e_i|`. -/
theorem opNorm_le_entries (L : T3 →L[ℝ] T3) : ‖L‖ ≤ ∑ j, ∑ i, |L (ev j) i| := by
  have hw : ∀ w : T3, ‖w‖ ≤ ∑ i, |w i| := fun w => by
    rw [EuclideanSpace.norm_eq]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    simp only [Real.norm_eq_abs, sq_abs]
    calc ∑ i, (w i) ^ 2 = ∑ i, |w i| ^ 2 := by simp
      _ ≤ (∑ i, |w i|) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => abs_nonneg _
  refine L.opNorm_le_bound (by positivity) fun y => ?_
  have hy : y = ∑ j, y j • ev j := by
    ext l; simp [ev, Finset.sum_apply, Pi.single_apply]
  have hyj : ∀ j, |y j| ≤ ‖y‖ := fun j => by
    simpa using PiLp.norm_apply_le y j
  calc ‖L y‖ = ‖∑ j, y j • L (ev j)‖ := by
        conv_lhs => rw [hy]
        simp [map_sum, map_smul]
    _ ≤ ∑ j, ‖y j • L (ev j)‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖y‖ * ∑ i, |L (ev j) i| := Finset.sum_le_sum fun j _ => by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (hyj j) (hw _) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by rw [← Finset.mul_sum, mul_comm]

/-- **Proved.** High-frequency tail of `∂_j v_i` by Cauchy–Schwarz (`s > 5/2`):
`∑_{|k|>R} |k_j||v̂_{k,i}| ≤ (tailWeight (s-1) R)^{1/2} ‖v‖_{H^s}`. -/
theorem grad_tail_le {s : ℝ} (hs : 5 / 2 < s) {v : VelocityField}
    (hu : IsPeriodicSmoothInitialData v) (R : ℝ) (i j : Fin 3) :
    ∑' k : Mode, (if modeSq k ≤ R ^ 2 then 0 else |(k j : ℝ)| * ‖fourierCoeffVF v k i‖) ≤
      Real.sqrt (tailWeight (s - 1) R) * Real.sqrt (hsSq s v) := by
  set c := fun k : Mode => |(k j : ℝ)| * ‖fourierCoeffVF v k i‖
  set f := fun k : Mode => if modeSq k ≤ R ^ 2 then 0 else Real.sqrt (sobW (-(s - 1)) k)
  set g := fun k : Mode => Real.sqrt (sobW (s - 1) k) * c k
  have hc0 : ∀ k, 0 ≤ c k := fun k => by positivity
  have hf0 : ∀ k, 0 ≤ f k := fun k => by simp only [f]; split_ifs <;> positivity
  have hg0 : ∀ k, 0 ≤ g k := fun k => by positivity
  have hf2 : ∀ k, f k ^ 2 = if modeSq k ≤ R ^ 2 then 0 else sobW (-(s - 1)) k := fun k => by
    simp only [f]; split_ifs <;> simp [Real.sq_sqrt (sobW_pos _ k).le]
  have hfs : Summable fun k => f k ^ 2 := by
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_)
      (summable_sobW_neg (s := s - 1) (by linarith))
    rw [hf2]; split_ifs <;> simp [(sobW_pos _ k).le]
  have hH := periodicDataHs s v hu
  unfold TorusFourierNS.MemHsField at hH
  have hHi : Summable fun k : Mode => sobW s k * ‖fourierCoeffVF v k i‖ ^ 2 :=
    hH.comp_injective (i := fun k => (k, i)) fun a b h => by simpa using h
  have hgle : ∀ k, g k ^ 2 ≤ sobW s k * ‖fourierCoeffVF v k i‖ ^ 2 := fun k => by
    have hp := one_add_sq_pos k
    have hkj : ((k j : ℝ)) ^ 2 ≤ 1 + ∑ l, ((k l : ℝ)) ^ 2 := by
      have := Finset.single_le_sum (f := fun l => ((k l : ℝ)) ^ 2) (fun l _ => sq_nonneg _)
        (Finset.mem_univ j)
      linarith
    simp only [g, c, mul_pow, Real.sq_sqrt (sobW_pos _ k).le, sq_abs]
    have : sobW s k = sobW (s - 1) k * (1 + ∑ l, ((k l : ℝ)) ^ 2) := by
      unfold sobW; rw [← Real.rpow_add_one hp.ne']; ring_nf
    rw [this, ← mul_assoc]
    gcongr
    exact Real.rpow_nonneg hp.le _
  have hgs : Summable fun k => g k ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hgle hHi
  obtain ⟨_, hcs⟩ := cs_tsum hf0 hg0 hfs hgs
  have hterm : ∀ k, (if modeSq k ≤ R ^ 2 then 0 else c k) = f k * g k := fun k => by
    simp only [f, g]; split_ifs
    · simp
    · rw [← mul_assoc, sqrt_sobW_neg_mul, one_mul]
  rw [tsum_congr hterm]
  refine hcs.trans ?_
  have e1 : ∑' k, f k ^ 2 = tailWeight (s - 1) R := by simp only [hf2, tailWeight]
  rw [e1]
  gcongr
  calc ∑' k, g k ^ 2 ≤ ∑' k, sobW s k * ‖fourierCoeffVF v k i‖ ^ 2 := hgs.tsum_le_tsum hgle hHi
    _ ≤ ∑' p : Mode × Fin 3, sobW s p.1 * ‖fourierCoeffVF v p.1 p.2‖ ^ 2 :=
        tsum_comp_le_tsum_of_inj (f := fun p : Mode × Fin 3 =>
          sobW s p.1 * ‖fourierCoeffVF v p.1 p.2‖ ^ 2) hH
          (fun p => mul_nonneg (sobW_pos _ _).le (sq_nonneg _)) (i := fun k => (k, i))
          (fun a b h => by simpa using h)
    _ = hsSq s v := by
        unfold hsSq hsNormField
        rw [Real.sq_sqrt (tsum_nonneg fun p => mul_nonneg (sobW_pos _ _).le (sq_nonneg _))]

lemma lowGrad_norm_le {v : VelocityField} (hu : IsPeriodicSmoothInitialData v) (R : ℝ)
    (i j : Fin 3) (x : T3) :
    ‖lowGrad R v x i j‖ ≤ ∑' k : Mode, 2 * Real.pi * (|(k j : ℝ)| * ‖fourierCoeffVF v k i‖) := by
  have hs := (summable_mode_mul_coeff hu i j).mul_left (2 * Real.pi)
  have hb : ∀ k, ‖(vpWeight R k : ℂ) * (gradCoeff v k i j * phase k x)‖ ≤
      2 * Real.pi * (|(k j : ℝ)| * ‖fourierCoeffVF v k i‖) := fun k => by
    rw [norm_mul, norm_mul, norm_phase, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (vpWeight_nonneg R k), norm_gradCoeff, mul_one]
    exact mul_le_of_le_one_left (by positivity) (vpWeight_le_one R k)
  have hs' : Summable fun k => ‖(vpWeight R k : ℂ) * (gradCoeff v k i j * phase k x)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hs
  rw [lowGrad_eq]
  exact (norm_tsum_le_tsum_norm hs').trans (hs'.tsum_le_tsum hb hs)

/-- **Proved.** Assembly of the Brezis–Gallouet/BKM log inequality: for `s > 5/2`, the
low-frequency Prop `PeriodicLowFreqVorticityBound` implies `PeriodicLogSobolevBKMBound s`.
No other hypothesis. -/
theorem periodicLogSobolevBKMBound_of_lowFreq {s : ℝ} (hs : 5 / 2 < s)
    (hL : PeriodicLowFreqVorticityBound) : PeriodicLogSobolevBKMBound s := by
  obtain ⟨KL, hKL, hlow⟩ := hL
  set s' := s / 2 + 1 / 4
  set δ := s - 1 - s'
  have hδ : 0 < δ := by simp only [δ, s']; linarith
  have hs' : 3 / 2 < s' := by simp only [s']; linarith
  set A := ∑' k : Mode, sobW (-s') k
  have hA : 0 ≤ A := tsum_nonneg fun k => (sobW_pos _ k).le
  set B := 9 * (2 * Real.pi * Real.sqrt A)
  have hB : 0 ≤ B := by positivity
  refine ⟨B + KL * (2 + 1 / δ), by positivity, fun v hu => ?_⟩
  set N := Real.sqrt (hsSq s v)
  have hN : 0 ≤ N := Real.sqrt_nonneg _
  have hN2 : N ^ 2 = hsSq s v := Real.sq_sqrt (hsSq_nonneg s v)
  have h1N : 0 < 1 + N := by linarith
  set R := 2 * (1 + N) ^ (1 / δ)
  have hR1 : 1 ≤ (1 + N) ^ (1 / δ) := Real.one_le_rpow (by linarith) (by positivity)
  have hR2 : 2 ≤ R := by simp only [R]; linarith
  have hR : 0 < R := by linarith
  -- the tail
  have htail : ∀ i j : Fin 3, ∑' k : Mode,
      (if modeSq k ≤ R ^ 2 then 0 else |(k j : ℝ)| * ‖fourierCoeffVF v k i‖) ≤ Real.sqrt A := by
    intro i j
    refine (grad_tail_le hs hu R i j).trans ?_
    have ht := tailWeight_le_rpow hs' (show s' ≤ s - 1 by linarith) hR
    have hRp : R ^ (-2 * (s - 1 - s')) ≤ ((1 + N) ^ 2)⁻¹ := by
      simp only [R]
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul h1N.le,
        show 1 / δ * (-2 * (s - 1 - s')) = -(2:ℝ) by rw [show s - 1 - s' = δ from rfl]; field_simp,
        Real.rpow_neg h1N.le, Real.rpow_two]
      have : (2:ℝ) ^ (-2 * (s - 1 - s')) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by simp only [δ] at hδ; linarith)
      have : 0 ≤ ((1 + N) ^ 2)⁻¹ := by positivity
      nlinarith
    have ht' : tailWeight (s - 1) R ≤ ((1 + N) ^ 2)⁻¹ * A :=
      ht.trans (mul_le_mul_of_nonneg_right hRp hA)
    have ht0 : 0 ≤ tailWeight (s - 1) R := tsum_nonneg fun k => by
      split_ifs <;> simp [(sobW_pos _ k).le]
    rw [← Real.sqrt_mul ht0]
    apply Real.sqrt_le_sqrt
    rw [← hN2]
    calc tailWeight (s - 1) R * N ^ 2 ≤ ((1 + N) ^ 2)⁻¹ * A * N ^ 2 := by gcongr
      _ = A * (N ^ 2 / (1 + N) ^ 2) := by ring
      _ ≤ A * 1 := by
          gcongr
          rw [div_le_one (by positivity)]; nlinarith
      _ = A := mul_one A
  -- the log
  set L := Real.log (1 + hsSq s v)
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith [hsSq_nonneg s v])
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hlogN : Real.log (1 + N) ≤ 1 + L := by
    have : Real.log (1 + N) ≤ Real.log (2 * (1 + hsSq s v)) :=
      Real.log_le_log h1N (by rw [← hN2]; nlinarith)
    rw [Real.log_mul (by norm_num) (by linarith [hsSq_nonneg s v])] at this
    linarith
  have hlogR : 1 + Real.log R ≤ (2 + 1 / δ) * (1 + L) := by
    simp only [R]
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow h1N]
    have : 1 / δ * Real.log (1 + N) ≤ 1 / δ * (1 + L) := by gcongr
    nlinarith
  set ω := vorticity_sup_norm (vorticity v)
  have hω : 0 ≤ ω := vorticity_sup_norm_nonneg _
  -- the low part
  have hbdd : BddAbove (range fun x : T3 => ∑ i, ∑ j, ‖lowGrad R v x i j‖) := by
    refine ⟨∑ i, ∑ j, ∑' k : Mode, 2 * Real.pi * (|(k j : ℝ)| * ‖fourierCoeffVF v k i‖), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => lowGrad_norm_le hu R i j x
  have hlowv := hlow R hR2 v hu
  unfold gradSupNorm
  refine ciSup_le fun x => ?_
  have hx : ‖fderiv ℝ v x‖ ≤ (∑ i, ∑ j, ‖lowGrad R v x i j‖) + B := by
    refine (opNorm_le_entries _).trans ?_
    rw [Finset.sum_comm]
    have : ∀ i j, |(fderiv ℝ v x (ev j)) i| ≤ ‖lowGrad R v x i j‖ + 2 * Real.pi * Real.sqrt A :=
      fun i j => (entry_le hu hR i j x).trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (htail i j) (by positivity)))
    calc ∑ i, ∑ j, |(fderiv ℝ v x (ev j)) i|
        ≤ ∑ i, ∑ j, (‖lowGrad R v x i j‖ + 2 * Real.pi * Real.sqrt A) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => this i j
      _ = _ := by simp [Finset.sum_add_distrib, B]; ring
  have hle : ∑ i, ∑ j, ‖lowGrad R v x i j‖ ≤ lowGradSup R v :=
    le_ciSup hbdd x
  have hX : 0 ≤ ω * (1 + L) := by positivity
  calc ‖fderiv ℝ v x‖ ≤ KL * (1 + Real.log R) * ω + B := by linarith
    _ ≤ KL * ((2 + 1 / δ) * (1 + L)) * ω + B := by gcongr
    _ ≤ (B + KL * (2 + 1 / δ)) * (1 + ω * (1 + L)) := by
        have : 0 ≤ KL * (2 + 1 / δ) := by positivity
        nlinarith [mul_nonneg hB hX]

/-- **Proved (conditional).** The BKM `H^s` control with only the tame Prop and the low-frequency
Prop as inputs. -/
theorem periodicBKMHsControl_of_tame_lowFreq {s : ℝ} (ν : ℝ) (hs : 5 / 2 < s)
    (htame : PeriodicTameHsBound s) (hL : PeriodicLowFreqVorticityBound) :
    PeriodicBKMHsControl ν s :=
  periodicBKMHsControl_of_bounds ν htame (periodicLogSobolevBKMBound_of_lowFreq hs hL)

/-! ### Kato–Ponce, Fourier side: energy identity + commutator split -/

/-- Coined. Nonlinear (transport + pressure) part of the Fourier NS field: `fourierNSField ν a`
plus the viscous term back. It does not depend on `ν`. -/
def nlField (a : FField) (k : Mode) (i : Fin 3) : ℂ :=
  fourierNSField 0 a k i

lemma fourierNSField_eq (ν : ℝ) (a : FField) (k : Mode) (i : Fin 3) :
    fourierNSField ν a k i = -((viscCoeff ν k : ℝ) : ℂ) * a k i + nlField a k i := by
  simp [fourierNSField, nlField, viscCoeff, sub_eq_add_neg]

/-- Coined. Weighted energy rate `∑_{k,i} ⟨k⟩^{2s} 2 Re(conj(a_{k,i}) F_{k,i})`. -/
def rateOf (s : ℝ) (F a : FField) : ℝ :=
  ∑' p : Mode × Fin 3, sobW s p.1 * (2 * ((starRingEnd ℂ) (a p.1 p.2) * F p.1 p.2).re)

/-- Coined. **Hypothesis (true, classical, not formalized).** `H^s` energy identity on the
Fourier side for classical periodic solutions: `t ↦ ‖u(t)‖²_{H^s}` is continuous and
`d/dt ‖u‖²_{H^s} = rateOf s (fourierNSField ν û) û`, with the rate summable. (Derivation: the
coefficients obey `û' = fourierNSField ν û`, by integrating NS against `e^{-2πik·x}`, plus
dominated termwise differentiation.) -/
def PeriodicFourierHsEnergyIdentity (ν s : ℝ) : Prop :=
  0 < ν → ∀ (u₀ : VelocityField) (u : TimeDependentVelocity) (p : TimeDependentPressure) (T' : ℝ),
    IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T' u p →
    ContinuousOn (fun t => hsSq s (u t)) (Icc 0 T') ∧
    ∀ t ∈ Ioo 0 T', Summable (fun p : Mode × Fin 3 => sobW s p.1 *
        (2 * ((starRingEnd ℂ) (fourierCoeffVF (u t) p.1 p.2) *
          fourierNSField ν (fourierCoeffVF (u t)) p.1 p.2).re)) ∧
      HasDerivAt (fun t => hsSq s (u t))
        (rateOf s (fourierNSField ν (fourierCoeffVF (u t))) (fourierCoeffVF (u t))) t

/-- Coined. **Hypothesis (true for some `C = C(s)`, `s > 5/2`; not formalized).** Fourier-side
Kato–Ponce commutator bound with `‖∇v‖_∞`: the nonlinear rate is summable and
`rateOf s (nlField v̂) v̂ ≤ C ‖∇v‖_∞ ‖v‖²_{H^s}`. Note: the Fourier-side machinery in
`TorusFourierNS` (`weight_commutator_le`, `galerkinTameTransportBound_of_gt`) gives this with
`‖v‖_{H^{s₀}}` (via the Wiener norm `∑|k||v̂_k|`) in place of `‖∇v‖_∞`; replacing it by
`‖∇v‖_∞` needs a physical-space paraproduct argument. -/
def PeriodicFourierCommutatorBound (s C : ℝ) : Prop :=
  ∀ v : VelocityField, IsPeriodicSmoothInitialData v →
    Summable (fun p : Mode × Fin 3 => sobW s p.1 *
        (2 * ((starRingEnd ℂ) (fourierCoeffVF v p.1 p.2) * nlField (fourierCoeffVF v) p.1 p.2).re)) ∧
    rateOf s (nlField (fourierCoeffVF v)) (fourierCoeffVF v) ≤ C * gradSupNorm v * hsSq s v

/-- **Proved.** The viscous part of the rate is `≤ 0` termwise (`ν ≥ 0`). -/
lemma visc_term_nonpos {ν : ℝ} (hν : 0 ≤ ν) (s : ℝ) (a : FField) (k : Mode) (i : Fin 3) :
    sobW s k * (2 * ((starRingEnd ℂ) (a k i) * (-((viscCoeff ν k : ℝ) : ℂ) * a k i)).re) ≤ 0 := by
  have hc := viscCoeff_nonneg hν k
  have : ((starRingEnd ℂ) (a k i) * (-((viscCoeff ν k : ℝ) : ℂ) * a k i)).re =
      -(viscCoeff ν k * ‖a k i‖ ^ 2) := by
    rw [show (starRingEnd ℂ) (a k i) * (-((viscCoeff ν k : ℝ) : ℂ) * a k i) =
        -((viscCoeff ν k : ℝ) : ℂ) * ((starRingEnd ℂ) (a k i) * a k i) by ring,
      Complex.conj_mul']
    simp [← Complex.ofReal_pow]
  rw [this]
  have := (sobW_pos s k).le
  nlinarith [mul_nonneg hc (sq_nonneg ‖a k i‖)]

open Corrected in
/-- **Proved.** `PeriodicTameHsInequality ν s C` from the Fourier `H^s` energy identity and the
Fourier commutator bound (the viscous part is dropped by its sign). -/
theorem periodicTameHsInequality_of_fourier {ν s C : ℝ}
    (hE : PeriodicFourierHsEnergyIdentity ν s) (hC : PeriodicFourierCommutatorBound s C) :
    PeriodicTameHsInequality ν s C := by
  intro hν u₀ u p T' hsol
  obtain ⟨hcont, hder⟩ := hE hν u₀ u p T' hsol
  refine ⟨hcont, fun t ht => ?_⟩
  obtain ⟨hsum, hd⟩ := hder t ht
  refine ⟨_, hd, ?_⟩
  have htI : t ∈ Icc (0:ℝ) T' := Ioo_subset_Icc_self ht
  have hut : IsPeriodicSmoothInitialData (u t) :=
    ⟨contDiff_slice hsol.2.2.2.1 htI, fun z => hsol.2.2.2.2.2.2.1 t htI z, hsol.2.1 t htI⟩
  obtain ⟨hnl, hbound⟩ := hC (u t) hut
  set a := fourierCoeffVF (u t)
  have hsplit : ∀ q : Mode × Fin 3, sobW s q.1 *
      (2 * ((starRingEnd ℂ) (a q.1 q.2) * fourierNSField ν a q.1 q.2).re) =
      sobW s q.1 * (2 * ((starRingEnd ℂ) (a q.1 q.2) * (-((viscCoeff ν q.1 : ℝ) : ℂ) * a q.1 q.2)).re)
      + sobW s q.1 * (2 * ((starRingEnd ℂ) (a q.1 q.2) * nlField a q.1 q.2).re) := fun q => by
    rw [fourierNSField_eq, mul_add, Complex.add_re]; ring
  have hvs : Summable fun q : Mode × Fin 3 => sobW s q.1 *
      (2 * ((starRingEnd ℂ) (a q.1 q.2) * (-((viscCoeff ν q.1 : ℝ) : ℂ) * a q.1 q.2)).re) := by
    have := hsum.sub hnl
    refine this.congr fun q => ?_
    simp only [hsplit]; ring
  have hv0 : ∑' q : Mode × Fin 3, sobW s q.1 *
      (2 * ((starRingEnd ℂ) (a q.1 q.2) * (-((viscCoeff ν q.1 : ℝ) : ℂ) * a q.1 q.2)).re) ≤ 0 :=
    tsum_nonpos fun q => visc_term_nonpos hν.le s a q.1 q.2
  have : rateOf s (fourierNSField ν a) a = (∑' q : Mode × Fin 3, sobW s q.1 *
      (2 * ((starRingEnd ℂ) (a q.1 q.2) * (-((viscCoeff ν q.1 : ℝ) : ℂ) * a q.1 q.2)).re))
      + rateOf s (nlField a) a := by
    unfold rateOf; rw [tsum_congr hsplit, hvs.tsum_add hnl]
  rw [this]
  linarith

/-- **Proved (conditional).** The BKM `H^s` control from the three Fourier/low-frequency Props, with
existential constants. -/
theorem periodicBKMHsControl_of_fourier_lowFreq {s : ℝ} (ν : ℝ) (hs : 5 / 2 < s)
    (hE : ∀ ν, PeriodicFourierHsEnergyIdentity ν s)
    (hC : ∃ C, 0 ≤ C ∧ PeriodicFourierCommutatorBound s C)
    (hL : PeriodicLowFreqVorticityBound) : PeriodicBKMHsControl ν s := by
  obtain ⟨C, hC0, hCb⟩ := hC
  exact periodicBKMHsControl_of_tame_lowFreq ν hs
    ⟨C, hC0, fun ν => periodicTameHsInequality_of_fourier (hE ν) hCb⟩ hL

end PeriodicNSContinuation
