/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.BKMPieces

/-!
# Brezis–Gallouet: tail rate, log choice of `R`, low-frequency Prop; Kato–Ponce start
(names coined)
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D TorusFourierNS

namespace PeriodicNSContinuation

/-! ### 1. Tail rate and the choice of `R` -/

lemma modeSq_nonneg (k : Mode) : 0 ≤ modeSq k := Finset.sum_nonneg fun i _ => sq_nonneg _

/-- **Proved.** Tail rate: for `3/2 < s' ≤ s` and `R > 0`,
`tailWeight s R ≤ R^{-2(s-s')} ∑_k (1+|k|²)^{-s'}`. -/
theorem tailWeight_le_rpow {s s' R : ℝ} (hs' : 3 / 2 < s') (hss : s' ≤ s) (hR : 0 < R) :
    tailWeight s R ≤ R ^ (-2 * (s - s')) * ∑' k : Mode, sobW (-s') k := by
  have hW := summable_sobW_neg hs'
  have hW2 := summable_sobW_neg (show 3 / 2 < s by linarith)
  have hterm : ∀ k : Mode, (if modeSq k ≤ R ^ 2 then 0 else sobW (-s) k) ≤
      R ^ (-2 * (s - s')) * sobW (-s') k := fun k => by
    split_ifs with h
    · exact mul_nonneg (by positivity) (sobW_pos _ k).le
    · rw [not_le] at h
      have hp := one_add_sq_pos k
      have hlt : R ^ 2 ≤ 1 + ∑ i, ((k i : ℝ)) ^ 2 := by unfold modeSq at h; linarith
      unfold sobW
      rw [show -s = -s' + -(s - s') by ring, Real.rpow_add hp, mul_comm]
      gcongr
      calc (1 + ∑ i, ((k i : ℝ)) ^ 2) ^ (-(s - s')) ≤ (R ^ 2) ^ (-(s - s')) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hlt (by linarith)
        _ = R ^ (-2 * (s - s')) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]; ring_nf
  have hsum : Summable fun k : Mode => if modeSq k ≤ R ^ 2 then 0 else sobW (-s) k :=
    Summable.of_nonneg_of_le (fun k => by split_ifs <;> simp [(sobW_pos _ k).le])
      (fun k => by split_ifs <;> simp [(sobW_pos _ k).le]) hW2
  unfold tailWeight
  rw [← tsum_mul_left]
  exact hsum.tsum_le_tsum hterm (hW.mul_left _)

/-- **Proved.** Choice of `R` giving the log. With `δ = s - s' > 0`, `N = ‖c‖_{H^s}`,
`R = (1+N)^{1/δ}`: `∑|c_k| ≤ ∑_{|k|≤R}|c_k| + (∑_k (1+|k|²)^{-s'})^{1/2}` and
`log R = log(1+N)/δ`. -/
theorem fourier_split_log {s s' : ℝ} (hs' : 3 / 2 < s') (hss : s' < s) (c : Mode → ℝ)
    (hc : Summable fun k => sobW s k * c k ^ 2) :
    let N := Real.sqrt (∑' k, sobW s k * c k ^ 2)
    let R := (1 + N) ^ (1 / (s - s'))
    ∑' k, |c k| ≤ ∑' k, (if modeSq k ≤ R ^ 2 then |c k| else 0) +
        Real.sqrt (∑' k : Mode, sobW (-s') k) ∧
      Real.log R = Real.log (1 + N) / (s - s') := by
  intro N R
  have hδ : 0 < s - s' := by linarith
  have hN : 0 ≤ N := Real.sqrt_nonneg _
  have h1N : 0 < 1 + N := by linarith
  have hR : 0 < R := Real.rpow_pos_of_pos h1N _
  set A := ∑' k : Mode, sobW (-s') k
  have hA : 0 ≤ A := tsum_nonneg fun k => (sobW_pos _ k).le
  refine ⟨(fourier_split_bound (by linarith) c hc R).2.trans ?_, ?_⟩
  · gcongr
    have ht := tailWeight_le_rpow hs' hss.le hR
    have hRp : R ^ (-2 * (s - s')) = ((1 + N) ^ 2)⁻¹ := by
      simp only [R]
      rw [← Real.rpow_mul h1N.le, show 1 / (s - s') * (-2 * (s - s')) = -(2:ℝ) by field_simp,
        Real.rpow_neg h1N.le, Real.rpow_two]
    rw [hRp] at ht
    have ht0 : 0 ≤ tailWeight s R := tsum_nonneg fun k => by
      split_ifs <;> simp [(sobW_pos _ k).le]
    rw [← Real.sqrt_mul ht0]
    apply Real.sqrt_le_sqrt
    have hNs : N ^ 2 = ∑' k, sobW s k * c k ^ 2 :=
      Real.sq_sqrt (tsum_nonneg fun k => mul_nonneg (sobW_pos _ k).le (sq_nonneg _))
    rw [← hNs]
    calc tailWeight s R * N ^ 2 ≤ ((1 + N) ^ 2)⁻¹ * A * N ^ 2 := by gcongr
      _ = A * (N ^ 2 / (1 + N) ^ 2) := by ring
      _ ≤ A * 1 := by
          gcongr
          rw [div_le_one (by positivity)]; nlinarith
      _ = A := mul_one A
  · simp only [R]
    rw [Real.log_rpow h1N]; ring

/-! ### 2. The low-frequency `‖ω‖_∞` step, as a named Prop -/

/-- Coined. Tensor de la Vallée Poussin weight: `∏_i min(1, max(0, 2 - |k_i|/R))`.
Equal to `1` on `|k|_∞ ≤ R`, `0` once some `|k_i| ≥ 2R`. -/
def vpWeight (R : ℝ) (k : Mode) : ℝ := ∏ i, min 1 (max 0 (2 - |(k i : ℝ)| / R))

lemma vpWeight_nonneg (R : ℝ) (k : Mode) : 0 ≤ vpWeight R k :=
  Finset.prod_nonneg fun i _ => le_min zero_le_one (le_max_left _ _)

lemma vpWeight_le_one (R : ℝ) (k : Mode) : vpWeight R k ≤ 1 :=
  Finset.prod_le_one (fun i _ => le_min zero_le_one (le_max_left _ _)) fun i _ => min_le_left _ _

lemma vpWeight_eq_one {R : ℝ} (hR : 0 < R) {k : Mode} (hk : ∀ i, |(k i : ℝ)| ≤ R) :
    vpWeight R k = 1 := by
  refine Finset.prod_eq_one fun i _ => min_eq_left ?_
  have : |(k i : ℝ)| / R ≤ 1 := (div_le_one hR).2 (hk i)
  exact le_max_of_le_right (by linarith)

lemma vpWeight_eq_zero {R : ℝ} (hR : 0 < R) {k : Mode} {i : Fin 3} (hk : 2 * R ≤ |(k i : ℝ)|) :
    vpWeight R k = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  have : 2 ≤ |(k i : ℝ)| / R := (le_div_iff₀ hR).2 (by linarith)
  rw [max_eq_left (by linarith), min_eq_right zero_le_one]

/-- Coined. Fourier coefficient of `∂_j v_i` at mode `k`: `2πi k_j v̂_{k,i}`. -/
def gradCoeff (v : VelocityField) (k : Mode) (i j : Fin 3) : ℂ :=
  2 * Real.pi * Complex.I * (k j : ℂ) * fourierCoeffVF v k i

/-- Coined. de la Vallée Poussin low-pass of `∂_j v_i` at `x` (a finite sum: `vpWeight R k = 0`
outside `|k|_∞ < 2R`). -/
def lowGrad (R : ℝ) (v : VelocityField) (x : T3) (i j : Fin 3) : ℂ :=
  ∑' k : Mode, (vpWeight R k : ℂ) * gradCoeff v k i j *
    Complex.exp (2 * Real.pi * Complex.I * ∑ l, ((k l : ℝ) : ℂ) * ((x l : ℝ) : ℂ))

/-- Coined. Sup norm of the low-pass gradient (entrywise sum norm). -/
def lowGradSup (R : ℝ) (v : VelocityField) : ℝ := ⨆ x : T3, ∑ i, ∑ j, ‖lowGrad R v x i j‖

/-- Coined. **Hypothesis (true, not formalized).** Low-frequency BKM step on `T³`:
`‖V_R ∇v‖_∞ ≤ K (1 + log R) ‖ω‖_∞` for `R ≥ 2`, smooth periodic divergence-free `v`, with
one absolute `K`. Classical proof: `V_R` has an `L¹`-bounded kernel (tensor Fejér); `∇v` is a
Calderón–Zygmund transform of `ω` (Biot–Savart, the `k=0` mode does not enter); split into
`O(log R)` smooth Littlewood–Paley blocks, each `L^∞`-bounded by `C‖ω‖_∞`. -/
def PeriodicLowFreqVorticityBound : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 2 ≤ R → ∀ v : VelocityField, IsPeriodicSmoothInitialData v →
    lowGradSup R v ≤ K * (1 + Real.log R) * vorticity_sup_norm (vorticity v)

/-- **Proved.** The arithmetic of Brezis–Gallouet: `g ≤ low + tail`, `low ≤ K(1+log R)ω`,
`tail ≤ B`, `log R = log(1+N)/δ` give `g ≤ K'(1 + ω(1+log(1+N)))` with
`K' = max (B) (K·max 1 (1/δ))`. -/
theorem bkm_log_arith {g low tail ω K B N R δ : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) (hω : 0 ≤ ω)
    (hN : 0 ≤ N) (hδ : 0 < δ) (hg : g ≤ low + tail) (hlow : low ≤ K * (1 + Real.log R) * ω)
    (htail : tail ≤ B) (hR : Real.log R = Real.log (1 + N) / δ) :
    g ≤ max B (K * max 1 (1 / δ)) * (1 + ω * (1 + Real.log (1 + N))) := by
  set M := max B (K * max 1 (1 / δ))
  have hL : 0 ≤ Real.log (1 + N) := Real.log_nonneg (by linarith)
  have h1 : Real.log R ≤ max 1 (1 / δ) * Real.log (1 + N) := by
    rw [hR, div_eq_mul_one_div, mul_comm]; gcongr; exact le_max_right _ _
  have hm1 : (1:ℝ) ≤ max 1 (1 / δ) := le_max_left _ _
  have hlow' : low ≤ K * max 1 (1 / δ) * (ω * (1 + Real.log (1 + N))) := by
    refine hlow.trans ?_
    have : 1 + Real.log R ≤ max 1 (1 / δ) * (1 + Real.log (1 + N)) := by nlinarith
    calc K * (1 + Real.log R) * ω ≤ K * (max 1 (1 / δ) * (1 + Real.log (1 + N))) * ω := by
          gcongr
      _ = _ := by ring
  have hX : 0 ≤ ω * (1 + Real.log (1 + N)) := by positivity
  have hM1 : B ≤ M := le_max_left _ _
  have hM2 : K * max 1 (1 / δ) ≤ M := le_max_right _ _
  nlinarith

/-! ### 3. Kato–Ponce, Fourier side (start) -/

lemma modeSq_add_le (a b : Mode) : modeSq (a + b) ≤ 2 * modeSq a + 2 * modeSq b := by
  unfold modeSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  push_cast [Pi.add_apply]
  nlinarith [sq_nonneg ((a i : ℝ) - b i)]

/-- **Proved.** Peetre-type splitting of the Sobolev weight (the frequency-splitting step of a
Fourier-side Kato–Ponce/tame product estimate): for `s ≥ 0`,
`(1+|a+b|²)^s ≤ 4^s ((1+|a|²)^s + (1+|b|²)^s)`. -/
theorem sobW_add_le {s : ℝ} (hs : 0 ≤ s) (a b : Mode) :
    sobW s (a + b) ≤ 4 ^ s * (sobW s a + sobW s b) := by
  have ha := one_add_sq_pos a
  have hb := one_add_sq_pos b
  set m := max (1 + ∑ i, ((a i : ℝ)) ^ 2) (1 + ∑ i, ((b i : ℝ)) ^ 2)
  have hab := modeSq_add_le a b
  unfold modeSq at hab
  have hle : 1 + ∑ i, (((a + b) i : ℤ) : ℝ) ^ 2 ≤ 4 * m := by
    have := le_max_left (1 + ∑ i, ((a i : ℝ)) ^ 2) (1 + ∑ i, ((b i : ℝ)) ^ 2)
    have := le_max_right (1 + ∑ i, ((a i : ℝ)) ^ 2) (1 + ∑ i, ((b i : ℝ)) ^ 2)
    linarith
  unfold sobW
  calc (1 + ∑ i, (((a + b) i : ℤ) : ℝ) ^ 2) ^ s ≤ (4 * m) ^ s :=
        Real.rpow_le_rpow (one_add_sq_pos _).le hle hs
    _ = 4 ^ s * m ^ s := Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ _ := by
        gcongr
        rcases le_total (1 + ∑ i, ((a i : ℝ)) ^ 2) (1 + ∑ i, ((b i : ℝ)) ^ 2) with h | h
        · rw [show m = _ from max_eq_right h]
          linarith [Real.rpow_nonneg ha.le s]
        · rw [show m = _ from max_eq_left h]
          linarith [Real.rpow_nonneg hb.le s]

/-- **Proved.** Pointwise weighted-convolution split: for `s ≥ 0`, each term of
`(1+|k|²)^{s/2} |∑_j â_{k-j} b̂_j|` obeys
`⟨k⟩^s |x||y| ≤ 2^s (⟨k-j⟩^s |x||y| + |x| ⟨j⟩^s |y|)` (here `⟨k⟩^s = sobW (s/2) k`). -/
theorem conv_term_split {s : ℝ} (hs : 0 ≤ s) (k j : Mode) (x y : ℝ) :
    sobW (s / 2) k * (|x| * |y|) ≤
      2 ^ s * (sobW (s / 2) (k - j) * |x| * |y| + |x| * (sobW (s / 2) j * |y|)) := by
  have h := sobW_add_le (s := s / 2) (by linarith) (k - j) j
  rw [sub_add_cancel] at h
  have h4 : (4:ℝ) ^ (s / 2) = 2 ^ s := by
    rw [show (4:ℝ) = 2 ^ (2:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; ring_nf
  rw [h4] at h
  have hxy : 0 ≤ |x| * |y| := by positivity
  calc sobW (s / 2) k * (|x| * |y|) ≤ 2 ^ s * (sobW (s / 2) (k - j) + sobW (s / 2) j) * (|x| * |y|) :=
        mul_le_mul_of_nonneg_right h hxy
    _ = _ := by ring

end PeriodicNSContinuation
