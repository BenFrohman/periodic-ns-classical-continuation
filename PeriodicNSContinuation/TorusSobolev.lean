/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import Mathlib

/-!
# Sobolev spaces `Hˢ` on the torus `UnitAddTorus (Fin 3)` by Fourier weights

`Hˢ` membership of a coefficient sequence `c : ℤ³ → ℂ` is summability of
`(1 + |k|²)ˢ ‖c k‖²`; for an `L²` function it is applied to `mFourierCoeff f`.
Proved here (no hypotheses): weight positivity and monotonicity in `s`; `Hᵗ ⊆ Hˢ` for `s ≤ t`
with the norm inequality; `Hˢ` is closed under `+` and scalar multiples; the squared norm is
`≥ 0` and vanishes only at the zero sequence; `H⁰ = L²` with `‖f‖²_{H⁰} = ∫ ‖f‖²` (Mathlib's
Parseval); and the Sobolev embedding: for `s > 3/2`, every `f ∈ L² ∩ Hˢ` has an a.e.
representative that is a continuous function, the uniform sum of its Fourier series.
Scalar (`ℂ`-valued) fields only; vector fields are componentwise and not done here.
-/

open MeasureTheory UnitAddTorus Real

namespace PeriodicNSContinuation

/-- The probability Haar measure on the unit circle, the same local instance Mathlib's
`Analysis.Fourier.AddCircleMulti` uses, so `L²` here is Mathlib's `L²(UnitAddTorus (Fin 3))`. -/
noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local notation "L²T3" => Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3)))

/-- `1 + |k|²` for `k ∈ ℤ³`. -/
noncomputable def jbracketSq (k : Fin 3 → ℤ) : ℝ := 1 + ∑ i, ((k i : ℝ)) ^ 2

theorem one_le_jbracketSq (k : Fin 3 → ℤ) : 1 ≤ jbracketSq k := by
  unfold jbracketSq; have : 0 ≤ ∑ i, ((k i : ℝ)) ^ 2 := by positivity
  linarith

theorem jbracketSq_pos (k : Fin 3 → ℤ) : 0 < jbracketSq k :=
  lt_of_lt_of_le one_pos (one_le_jbracketSq k)

/-- Sobolev weight `(1 + |k|²)ˢ`. -/
noncomputable def sobolevWeight (s : ℝ) (k : Fin 3 → ℤ) : ℝ := jbracketSq k ^ s

theorem sobolevWeight_pos (s : ℝ) (k : Fin 3 → ℤ) : 0 < sobolevWeight s k :=
  rpow_pos_of_pos (jbracketSq_pos k) s

theorem sobolevWeight_zero (k : Fin 3 → ℤ) : sobolevWeight 0 k = 1 := by
  simp [sobolevWeight]

theorem sobolevWeight_neg (s : ℝ) (k : Fin 3 → ℤ) :
    sobolevWeight (-s) k = (sobolevWeight s k)⁻¹ :=
  rpow_neg (jbracketSq_pos k).le s

/-- Monotonicity of the weight in `s`. -/
theorem sobolevWeight_mono {s t : ℝ} (h : s ≤ t) (k : Fin 3 → ℤ) :
    sobolevWeight s k ≤ sobolevWeight t k :=
  rpow_le_rpow_of_exponent_le (one_le_jbracketSq k) h

/-- `Hˢ` membership of a coefficient sequence. -/
def MemSobolevSeq (s : ℝ) (c : (Fin 3 → ℤ) → ℂ) : Prop :=
  Summable fun k => sobolevWeight s k * ‖c k‖ ^ 2

/-- Squared `Hˢ` norm of a coefficient sequence. -/
noncomputable def sobolevNormSqSeq (s : ℝ) (c : (Fin 3 → ℤ) → ℂ) : ℝ :=
  ∑' k, sobolevWeight s k * ‖c k‖ ^ 2

/-- `Hˢ` membership of an `L²` function on `𝕋³`, through its Fourier coefficients. -/
def MemSobolev (s : ℝ) (f : L²T3) : Prop := MemSobolevSeq s (mFourierCoeff f)

/-- Squared `Hˢ` norm of an `L²` function on `𝕋³`. -/
noncomputable def sobolevNormSq (s : ℝ) (f : L²T3) : ℝ := sobolevNormSqSeq s (mFourierCoeff f)

theorem sobolevNormSqSeq_nonneg (s : ℝ) (c : (Fin 3 → ℤ) → ℂ) : 0 ≤ sobolevNormSqSeq s c :=
  tsum_nonneg fun k => mul_nonneg (sobolevWeight_pos s k).le (by positivity)

theorem sobolevNormSqSeq_eq_zero_iff {s : ℝ} {c : (Fin 3 → ℤ) → ℂ} (hc : MemSobolevSeq s c) :
    sobolevNormSqSeq s c = 0 ↔ c = 0 := by
  constructor
  · intro h; funext k
    have hs : HasSum (fun k => sobolevWeight s k * ‖c k‖ ^ 2) 0 := h ▸ hc.hasSum
    rw [hasSum_zero_iff_of_nonneg (fun k => mul_nonneg (sobolevWeight_pos s k).le
      (by positivity))] at hs
    have := congrFun hs k
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd h1 (sobolevWeight_pos s k).ne'
    · simpa using h1
  · rintro rfl; simp [sobolevNormSqSeq]

/-- `Hᵗ ⊆ Hˢ` for `s ≤ t`. -/
theorem MemSobolevSeq.mono {s t : ℝ} (h : s ≤ t) {c : (Fin 3 → ℤ) → ℂ}
    (hc : MemSobolevSeq t c) : MemSobolevSeq s c :=
  hc.of_nonneg_of_le (fun k => mul_nonneg (sobolevWeight_pos s k).le (by positivity))
    fun k => mul_le_mul_of_nonneg_right (sobolevWeight_mono h k) (by positivity)

theorem sobolevNormSqSeq_mono {s t : ℝ} (h : s ≤ t) {c : (Fin 3 → ℤ) → ℂ}
    (hc : MemSobolevSeq t c) : sobolevNormSqSeq s c ≤ sobolevNormSqSeq t c :=
  (hc.mono h).tsum_le_tsum
    (fun k => mul_le_mul_of_nonneg_right (sobolevWeight_mono h k) (by positivity)) hc

theorem MemSobolevSeq.smul {s : ℝ} {c : (Fin 3 → ℤ) → ℂ} (hc : MemSobolevSeq s c) (a : ℂ) :
    MemSobolevSeq s (a • c) := by
  unfold MemSobolevSeq at *
  convert hc.mul_left (‖a‖ ^ 2) using 1
  funext k; simp [mul_pow]; ring

theorem sobolevNormSqSeq_smul (s : ℝ) (c : (Fin 3 → ℤ) → ℂ) (a : ℂ) :
    sobolevNormSqSeq s (a • c) = ‖a‖ ^ 2 * sobolevNormSqSeq s c := by
  unfold sobolevNormSqSeq; rw [← tsum_mul_left]
  congr 1; funext k; simp [mul_pow]; ring

theorem MemSobolevSeq.add {s : ℝ} {c d : (Fin 3 → ℤ) → ℂ} (hc : MemSobolevSeq s c)
    (hd : MemSobolevSeq s d) : MemSobolevSeq s (c + d) := by
  unfold MemSobolevSeq at *
  refine ((hc.mul_left 2).add (hd.mul_left 2)).of_nonneg_of_le
    (fun k => mul_nonneg (sobolevWeight_pos s k).le (by positivity)) fun k => ?_
  have hw := (sobolevWeight_pos s k).le
  have h1 : ‖(c + d) k‖ ^ 2 ≤ 2 * ‖c k‖ ^ 2 + 2 * ‖d k‖ ^ 2 := by
    have := norm_add_le (c k) (d k)
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (‖c k‖ - ‖d k‖), norm_nonneg (c k + d k)]
  nlinarith

set_option backward.isDefEq.respectTransparency false in
/-- `H⁰ = L²`: every `L²` function is in `H⁰`, with `‖f‖²_{H⁰} = ∫ ‖f‖²` (Parseval). -/
theorem memSobolev_zero (f : L²T3) : MemSobolev 0 f := by
  have h := (hasSum_sq_mFourierCoeff f).summable
  unfold MemSobolev MemSobolevSeq
  simp only [sobolevWeight_zero, one_mul]
  exact h

set_option backward.isDefEq.respectTransparency false in
theorem sobolevNormSq_zero (f : L²T3) : sobolevNormSq 0 f = ∫ t, ‖f t‖ ^ 2 := by
  have h := (hasSum_sq_mFourierCoeff f).tsum_eq
  unfold sobolevNormSq sobolevNormSqSeq
  simp only [sobolevWeight_zero, one_mul]
  exact h

/-- For `s ≥ 0`, `Hˢ ⊆ L²` in norm: `∫ ‖f‖² ≤ ‖f‖²_{Hˢ}`. -/
theorem integral_sq_le_sobolevNormSq {s : ℝ} (hs : 0 ≤ s) {f : L²T3} (hf : MemSobolev s f) :
    ∫ t, ‖f t‖ ^ 2 ≤ sobolevNormSq s f := by
  rw [← sobolevNormSq_zero]; exact sobolevNormSqSeq_mono hs hf

/-! ## Summability of the weights for `s > 3/2` -/

theorem summable_one_add_sq_rpow {r : ℝ} (hr : 1 / 2 < r) :
    Summable fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ (-r) := by
  have h1 : Summable fun n : ℤ => |(n : ℝ)| ^ (-(2 * r)) := summable_abs_int_rpow (by linarith)
  have h2 : Summable fun n : ℤ => if n = 0 then (1 : ℝ) else 0 :=
    (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  refine (h1.add h2).of_nonneg_of_le (fun n => by positivity) fun n => ?_
  by_cases hn : n = 0
  · subst hn; simp
    positivity
  · simp only [hn, if_false, add_zero]
    have hpos : 0 < |(n : ℝ)| := abs_pos.2 (by exact_mod_cast hn)
    rw [show |(n : ℝ)| ^ (-(2 * r)) = (|(n : ℝ)| ^ (2 : ℝ)) ^ (-r) by
      rw [← rpow_mul hpos.le]; ring_nf]
    refine rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
    rw [rpow_two, sq_abs]; linarith

/-- The product bound `(1+|k|²)^{-s} ≤ ∏ᵢ (1+kᵢ²)^{-s/3}` for `s ≥ 0`. -/
theorem sobolevWeight_neg_le_prod {s : ℝ} (hs : 0 ≤ s) (k : Fin 3 → ℤ) :
    sobolevWeight (-s) k ≤ ∏ i, (1 + ((k i : ℝ)) ^ 2) ^ (-(s / 3)) := by
  have hA := jbracketSq_pos k
  have hle : ∀ i, 1 + ((k i : ℝ)) ^ 2 ≤ jbracketSq k := fun i => by
    unfold jbracketSq
    have := Finset.single_le_sum (f := fun j => ((k j : ℝ)) ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ i)
    linarith
  rw [Real.finset_prod_rpow _ _ (fun i _ => by positivity)]
  have hprod : ∏ i, (1 + ((k i : ℝ)) ^ 2) ≤ jbracketSq k ^ (3 : ℕ) := by
    rw [Fin.prod_univ_three]
    have h0 := hle 0; have h1 := hle 1; have h2 := hle 2
    calc (1 + ((k 0 : ℝ)) ^ 2) * (1 + ((k 1 : ℝ)) ^ 2) * (1 + ((k 2 : ℝ)) ^ 2)
        ≤ jbracketSq k * jbracketSq k * jbracketSq k := by gcongr
      _ = jbracketSq k ^ (3 : ℕ) := by ring
  have hp : 0 < ∏ i, (1 + ((k i : ℝ)) ^ 2) := Finset.prod_pos fun i _ => by positivity
  calc sobolevWeight (-s) k = (jbracketSq k ^ (3 : ℕ)) ^ (-(s / 3)) := by
        unfold sobolevWeight; rw [← rpow_natCast, ← rpow_mul hA.le]; norm_num; ring_nf
    _ ≤ (∏ i, (1 + ((k i : ℝ)) ^ 2)) ^ (-(s / 3)) :=
        rpow_le_rpow_of_nonpos hp hprod (by linarith)

/-- `∑_{k ∈ ℤ³} (1+|k|²)^{-s} < ∞` for `s > 3/2`. -/
theorem summable_sobolevWeight_neg {s : ℝ} (hs : 3 / 2 < s) :
    Summable fun k : Fin 3 → ℤ => sobolevWeight (-s) k := by
  set g : ℤ → ℝ := fun n => (1 + (n : ℝ) ^ 2) ^ (-(s / 3))
  have hg : Summable g := summable_one_add_sq_rpow (by linarith)
  have hg0 : ∀ n, 0 ≤ g n := fun n => by positivity
  let e : (Fin 3 → ℤ) ≃ ℤ × ℤ × ℤ :=
    { toFun := fun k => (k 0, k 1, k 2)
      invFun := fun p => ![p.1, p.2.1, p.2.2]
      left_inv := fun k => by funext i; fin_cases i <;> rfl
      right_inv := fun p => rfl }
  have hprod : Summable fun p : ℤ × ℤ × ℤ => g p.1 * (g p.2.1 * g p.2.2) :=
    hg.mul_of_nonneg (hg.mul_of_nonneg hg hg0 hg0) hg0
      (fun p => mul_nonneg (hg0 _) (hg0 _))
  have hP : Summable fun k : Fin 3 → ℤ => ∏ i, g (k i) := by
    have := (e.summable_iff).2 hprod
    refine this.congr fun k => ?_
    simp [e, Fin.prod_univ_three, mul_assoc]
  exact hP.of_nonneg_of_le (fun k => (sobolevWeight_pos _ k).le)
    fun k => sobolevWeight_neg_le_prod (by linarith) k

/-- For `s > 3/2`, `Hˢ` coefficients are absolutely summable. -/
theorem MemSobolevSeq.summable_norm {s : ℝ} (hs : 3 / 2 < s) {c : (Fin 3 → ℤ) → ℂ}
    (hc : MemSobolevSeq s c) : Summable fun k => ‖c k‖ := by
  refine (((show Summable _ from hc).add (summable_sobolevWeight_neg hs)).div_const 2).of_nonneg_of_le
    (fun k => norm_nonneg _) fun k => ?_
  have hw := sobolevWeight_pos s k
  rw [sobolevWeight_neg, le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
  have key : ‖c k‖ * 2 * sobolevWeight s k ≤
      (sobolevWeight s k * ‖c k‖ ^ 2 + (sobolevWeight s k)⁻¹) * sobolevWeight s k := by
    rw [add_mul, inv_mul_cancel₀ hw.ne']
    nlinarith [sq_nonneg (sobolevWeight s k * ‖c k‖ - 1)]
  exact le_of_mul_le_mul_right key hw

set_option backward.isDefEq.respectTransparency false in
/-- **Sobolev embedding `Hˢ(𝕋³) ⊂ C(𝕋³)` for `s > 3/2`.** An `L²` function in `Hˢ` equals a.e.
the continuous function `g`, and its Fourier series converges to `g` uniformly. -/
theorem sobolev_embedding_continuous {s : ℝ} (hs : 3 / 2 < s) (f : L²T3) (hf : MemSobolev s f) :
    ∃ g : C(UnitAddTorus (Fin 3), ℂ),
      HasSum (fun k => mFourierCoeff f k • mFourier k) g ∧ g.toLp 2 volume ℂ = f := by
  have hn : Summable fun k => ‖mFourierCoeff f k • mFourier k‖ := by
    simpa [norm_smul, mFourier_norm] using hf.summable_norm hs
  obtain ⟨g, hg⟩ := hn.of_norm
  refine ⟨g, hg, ?_⟩
  have h1 := (ContinuousMap.toLp (E := ℂ) 2 volume ℂ).hasSum hg
  simp only [map_smul] at h1
  exact h1.unique (hasSum_mFourier_series_L2 f)

end PeriodicNSContinuation
