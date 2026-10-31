/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.EnstrophyRate

/-!
# A uniform lattice sum on `ℤ³`

`latticeSum_le` — **proved**: for every `μ > 0`,
`∑_{k ∈ ℤ³} μ / (⟨k⟩² (μ² + ⟨k⟩²)) ≤ 12000`, where `⟨k⟩² = 1 + |k|²`.
This is the Fourier-side counting fact behind the 3D Ladyzhenskaya/Agmon-type interpolation
`‖â‖_{ℓ¹}⁴ ≲ ‖u‖²_{H¹} ‖u‖²_{H²}` used in `Ladyzhenskaya.lean`. The constant is not optimized.
-/

noncomputable section
open Set Filter Topology Finset

namespace PeriodicNSContinuation

/-- **Proved.** Telescoping bound for the partial sums of `1/(c² + i²)`. -/
lemma sum_range_inv_le {c : ℝ} (hc : 1 ≤ c) (n : ℕ) :
    ∑ i ∈ range n, 1 / (c ^ 2 + (i:ℝ) ^ 2) ≤ 5 / c - 4 / (c + n) := by
  induction n with
  | zero => simp; rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
  | succ n ih =>
    rw [sum_range_succ]
    have hn : (0:ℝ) ≤ n := n.cast_nonneg
    have key : 1 / (c ^ 2 + (n:ℝ) ^ 2) ≤ 4 / (c + n) - 4 / (c + (n + 1 : ℕ)) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith [sq_nonneg (c - n), mul_pos (by linarith : (0:ℝ) < c + n) (by linarith : (0:ℝ) < c + n)]
    linarith

lemma ennreal_tsum_nat_le {c : ℝ} (hc : 1 ≤ c) :
    ∑' n : ℕ, ENNReal.ofReal (1 / (c ^ 2 + (n:ℝ) ^ 2)) ≤ ENNReal.ofReal (5 / c) := by
  refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  refine ENNReal.ofReal_le_ofReal ((sum_range_inv_le hc n).trans ?_)
  have : 0 ≤ 4 / (c + n) := by have := n.cast_nonneg (α := ℝ); positivity
  linarith

/-- **Proved.** `∑_{n ∈ ℤ} 1/(c² + n²) ≤ 10/c` for `c ≥ 1`. -/
lemma ennreal_tsum_int_le {c : ℝ} (hc : 1 ≤ c) :
    ∑' n : ℤ, ENNReal.ofReal (1 / (c ^ 2 + (n:ℝ) ^ 2)) ≤ ENNReal.ofReal (10 / c) := by
  rw [tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable]
  have h2 : ∑' n : ℕ, ENNReal.ofReal (1 / (c ^ 2 + (((-(n + 1 : ℤ)) : ℤ) : ℝ) ^ 2)) ≤
      ∑' n : ℕ, ENNReal.ofReal (1 / (c ^ 2 + (n:ℝ) ^ 2)) := by
    refine ENNReal.tsum_le_tsum fun n => ENNReal.ofReal_le_ofReal ?_
    have hn : (0:ℝ) ≤ n := n.cast_nonneg
    push_cast
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  calc _ ≤ ENNReal.ofReal (5 / c) + ENNReal.ofReal (5 / c) := by
        simp only [Int.cast_natCast] at h2 ⊢
        exact add_le_add (ennreal_tsum_nat_le hc) (h2.trans (ennreal_tsum_nat_le hc))
    _ = ENNReal.ofReal (10 / c) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

/-- **Proved.** For `A ≥ 1`: `∑_{b ∈ ℤ} 2A/(A + b²) ≤ 20 √A`. -/
lemma ennreal_tsum_lorentz {A : ℝ} (hA : 1 ≤ A) :
    ∑' b : ℤ, ENNReal.ofReal (2 * A / (A + (b:ℝ) ^ 2)) ≤ ENNReal.ofReal (20 * Real.sqrt A) := by
  have hc : 1 ≤ Real.sqrt A := by rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hA
  have hsq : Real.sqrt A ^ 2 = A := Real.sq_sqrt (by linarith)
  have e : ∀ b : ℤ, ENNReal.ofReal (2 * A / (A + (b:ℝ) ^ 2)) =
      ENNReal.ofReal (2 * A) * ENNReal.ofReal (1 / (Real.sqrt A ^ 2 + (b:ℝ) ^ 2)) := fun b => by
    rw [← ENNReal.ofReal_mul (by linarith), hsq]; ring_nf
  simp_rw [e, ENNReal.tsum_mul_left]
  calc _ ≤ ENNReal.ofReal (2 * A) * ENNReal.ofReal (10 / Real.sqrt A) := by
        gcongr; exact ennreal_tsum_int_le hc
    _ = ENNReal.ofReal (20 * Real.sqrt A) := by
        rw [← ENNReal.ofReal_mul (by linarith)]; congr 1
        have : 0 < Real.sqrt A := by linarith
        field_simp; nlinarith [hsq]

/-- Coined. The weight `μ / (s(μ² + s))`, `s = 1 + a² + b² + c²`. -/
def latW (μ : ℝ) (s : ℝ) : ℝ := μ / (s * (μ ^ 2 + s))

lemma latW_anti {μ s t : ℝ} (hμ : 0 < μ) (hs : 1 ≤ s) (hst : s ≤ t) : latW μ t ≤ latW μ s := by
  unfold latW
  exact div_le_div_of_nonneg_left hμ.le (by positivity)
    (mul_le_mul hst (by linarith) (by positivity) (by linarith))

/-- Coined. One piece of the max-coordinate splitting. -/
def latL (μ : ℝ) (a b c : ℤ) : ENNReal :=
  ENNReal.ofReal (latW μ (1 + (a:ℝ) ^ 2)) *
    ENNReal.ofReal (2 * (1 + (a:ℝ) ^ 2) / ((1 + (a:ℝ) ^ 2) + (b:ℝ) ^ 2)) *
    ENNReal.ofReal (2 * (1 + (a:ℝ) ^ 2) / ((1 + (a:ℝ) ^ 2) + (c:ℝ) ^ 2))

lemma latW_le_latL {μ : ℝ} (hμ : 0 < μ) {a b c : ℤ} (hb : (b:ℝ) ^ 2 ≤ (a:ℝ) ^ 2)
    (hc : (c:ℝ) ^ 2 ≤ (a:ℝ) ^ 2) :
    ENNReal.ofReal (latW μ (1 + (a:ℝ) ^ 2 + (b:ℝ) ^ 2 + (c:ℝ) ^ 2)) ≤ latL μ a b c := by
  set A := 1 + (a:ℝ) ^ 2
  have hA : 1 ≤ A := by simp only [A]; nlinarith [sq_nonneg (a:ℝ)]
  have hb0 := sq_nonneg (b:ℝ); have hc0 := sq_nonneg (c:ℝ)
  have h1 : 1 ≤ 2 * A / (A + (b:ℝ) ^ 2) := by rw [le_div_iff₀ (by linarith)]; linarith
  have h2 : 1 ≤ 2 * A / (A + (c:ℝ) ^ 2) := by rw [le_div_iff₀ (by linarith)]; linarith
  unfold latL
  rw [← ENNReal.ofReal_mul (by unfold latW; positivity), ← ENNReal.ofReal_mul (by
    unfold latW; positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hW : latW μ (A + (b:ℝ) ^ 2 + (c:ℝ) ^ 2) ≤ latW μ A := latW_anti hμ hA (by linarith)
  have hW0 : 0 ≤ latW μ A := by unfold latW; positivity
  calc latW μ (A + (b:ℝ) ^ 2 + (c:ℝ) ^ 2) ≤ latW μ A := hW
    _ ≤ latW μ A * (2 * A / (A + (b:ℝ) ^ 2)) * (2 * A / (A + (c:ℝ) ^ 2)) := by
      have := mul_le_mul h1 h2 zero_le_one (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left this hW0]

lemma tsum_latL {μ : ℝ} (hμ : 0 < μ) :
    ∑' a : ℤ, ∑' b : ℤ, ∑' c : ℤ, latL μ a b c ≤ ENNReal.ofReal 4000 := by
  have hrow : ∀ a : ℤ, ∑' b : ℤ, ∑' c : ℤ, latL μ a b c ≤
      ENNReal.ofReal (400 * μ * (1 / (Real.sqrt (μ ^ 2 + 1) ^ 2 + (a:ℝ) ^ 2))) := fun a => by
    set A := 1 + (a:ℝ) ^ 2
    have hA : 1 ≤ A := by simp only [A]; nlinarith [sq_nonneg (a:ℝ)]
    unfold latL
    simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
    have hL := ennreal_tsum_lorentz hA
    calc _ ≤ ENNReal.ofReal (latW μ A) * ENNReal.ofReal (20 * Real.sqrt A) *
          ENNReal.ofReal (20 * Real.sqrt A) := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by unfold latW; positivity),
          ← ENNReal.ofReal_mul (by unfold latW; positivity)]
        congr 1
        rw [Real.sq_sqrt (by positivity)]
        have hs : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt (by linarith)
        unfold latW
        field_simp
        nlinarith [hs]
  calc _ ≤ ∑' a : ℤ, ENNReal.ofReal (400 * μ) *
        ENNReal.ofReal (1 / (Real.sqrt (μ ^ 2 + 1) ^ 2 + (a:ℝ) ^ 2)) :=
        ENNReal.tsum_le_tsum fun a => (hrow a).trans_eq (ENNReal.ofReal_mul (by positivity))
    _ ≤ ENNReal.ofReal (400 * μ) * ENNReal.ofReal (10 / Real.sqrt (μ ^ 2 + 1)) := by
        rw [ENNReal.tsum_mul_left]; gcongr
        refine ennreal_tsum_int_le ?_
        have := Real.sqrt_le_sqrt (show (1:ℝ) ≤ μ ^ 2 + 1 by nlinarith)
        simpa using this
    _ ≤ ENNReal.ofReal 4000 := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hμs : μ ≤ Real.sqrt (μ ^ 2 + 1) := by
          have := Real.sqrt_le_sqrt (show μ ^ 2 ≤ μ ^ 2 + 1 by linarith)
          rwa [Real.sqrt_sq hμ.le] at this
        have hp : 0 < Real.sqrt (μ ^ 2 + 1) := by positivity
        rw [mul_div_assoc', div_le_iff₀ hp]; nlinarith

/-- The equivalence `ℤ³ ≃ Mode` used for reindexing (coined). -/
def modeEquiv : ℤ × ℤ × ℤ ≃ TorusFourierNS.Mode where
  toFun p := ![p.1, p.2.1, p.2.2]
  invFun k := (k 0, k 1, k 2)
  left_inv p := by simp
  right_inv k := by funext i; fin_cases i <;> simp

/-- Coined. `⟨k⟩² = 1 + |k|²` as a real number. -/
def jsq (k : TorusFourierNS.Mode) : ℝ := 1 + ∑ i, ((k i : ℤ) : ℝ) ^ 2

lemma one_le_jsq (k : TorusFourierNS.Mode) : 1 ≤ jsq k := by
  unfold jsq; have : 0 ≤ ∑ i, ((k i : ℤ) : ℝ) ^ 2 := by positivity
  linarith

/-- **Proved.** Uniform lattice sum: `∑_{k ∈ ℤ³} μ/(⟨k⟩²(μ² + ⟨k⟩²)) ≤ 12000` for `μ > 0`. -/
theorem latticeSum_le {μ : ℝ} (hμ : 0 < μ) :
    ∑' k : TorusFourierNS.Mode, ENNReal.ofReal (latW μ (jsq k)) ≤ ENNReal.ofReal 12000 := by
  rw [← modeEquiv.tsum_eq, ENNReal.tsum_prod', ]
  simp_rw [ENNReal.tsum_prod']
  have hj : ∀ a b c : ℤ, jsq (modeEquiv (a, b, c)) = 1 + (a:ℝ) ^ 2 + (b:ℝ) ^ 2 + (c:ℝ) ^ 2 :=
    fun a b c => by simp [jsq, modeEquiv, Fin.sum_univ_three]; ring
  have hpt : ∀ a b c : ℤ, ENNReal.ofReal (latW μ (jsq (modeEquiv (a, b, c)))) ≤
      latL μ a b c + latL μ b a c + latL μ c a b := fun a b c => by
    rw [hj]
    have eB : (1:ℝ) + a ^ 2 + b ^ 2 + c ^ 2 = 1 + b ^ 2 + a ^ 2 + c ^ 2 := by ring
    have eC : (1:ℝ) + a ^ 2 + b ^ 2 + c ^ 2 = 1 + c ^ 2 + a ^ 2 + b ^ 2 := by ring
    rcases le_total ((b:ℝ) ^ 2) ((a:ℝ) ^ 2) with hab | hab <;>
    rcases le_total ((c:ℝ) ^ 2) ((a:ℝ) ^ 2) with hac | hac <;>
    rcases le_total ((c:ℝ) ^ 2) ((b:ℝ) ^ 2) with hbc | hbc
    all_goals first
      | (have h := latW_le_latL hμ (a := a) (b := b) (c := c) (by linarith) (by linarith)
         exact le_add_right (le_add_right h))
      | (have h := latW_le_latL hμ (a := b) (b := a) (c := c) (by linarith) (by linarith)
         rw [eB]; exact le_add_right (le_add_left h))
      | (have h := latW_le_latL hμ (a := c) (b := a) (c := b) (by linarith) (by linarith)
         rw [eC]; exact le_add_left h)
  calc _ ≤ ∑' a : ℤ, ∑' b : ℤ, ∑' c : ℤ, (latL μ a b c + latL μ b a c + latL μ c a b) :=
        ENNReal.tsum_le_tsum fun a => ENNReal.tsum_le_tsum fun b => ENNReal.tsum_le_tsum
          fun c => hpt a b c
    _ = (∑' a : ℤ, ∑' b : ℤ, ∑' c : ℤ, latL μ a b c) + (∑' a : ℤ, ∑' b : ℤ, ∑' c : ℤ, latL μ b a c)
        + (∑' a : ℤ, ∑' b : ℤ, ∑' c : ℤ, latL μ c a b) := by
        simp only [ENNReal.tsum_add]
    _ = (∑' a : ℤ, ∑' b : ℤ, ∑' c : ℤ, latL μ a b c) + (∑' a : ℤ, ∑' b : ℤ, ∑' c : ℤ, latL μ a b c)
        + (∑' a : ℤ, ∑' b : ℤ, ∑' c : ℤ, latL μ a b c) := by
        have h2 : (∑' a : ℤ, ∑' b : ℤ, ∑' c : ℤ, latL μ b a c)
            = ∑' a : ℤ, ∑' b : ℤ, ∑' c : ℤ, latL μ a b c := ENNReal.tsum_comm
        have h3 : (∑' a : ℤ, ∑' b : ℤ, ∑' c : ℤ, latL μ c a b)
            = ∑' a : ℤ, ∑' b : ℤ, ∑' c : ℤ, latL μ a b c := by
          have : ∀ a : ℤ, (∑' b : ℤ, ∑' c : ℤ, latL μ c a b) = ∑' c : ℤ, ∑' b : ℤ, latL μ c a b :=
            fun a => ENNReal.tsum_comm
          simp_rw [this]; exact ENNReal.tsum_comm
        rw [h2, h3]
    _ ≤ ENNReal.ofReal 4000 + ENNReal.ofReal 4000 + ENNReal.ofReal 4000 := by
        gcongr <;> exact tsum_latL hμ
    _ = ENNReal.ofReal 12000 := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
          ← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num

end PeriodicNSContinuation
