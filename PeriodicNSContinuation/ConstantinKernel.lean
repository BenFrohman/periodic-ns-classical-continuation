/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.DirectionEvolution

/-!
# Constantin's kernel for the bending vector (part (A) of the Frohmanian Tether Hypothesis)
-/

noncomputable section
open scoped RealInnerProductSpace

namespace PeriodicNSContinuation

local notation "V3" => EuclideanSpace ℝ (Fin 3)

/-- Coined. Cross product on `ℝ³`. -/
def cross3 (a b : V3) : V3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm
    ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

@[simp] lemma cross3_apply (a b : V3) (i : Fin 3) : cross3 a b i =
    ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0] i := rfl

lemma inner3 (a b : V3) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, real_inner_scalar, mul_comm]

theorem cross3_add (a b c : V3) : cross3 a (b + c) = cross3 a b + cross3 a c := by
  ext i; fin_cases i <;> simp <;> ring
theorem cross3_smul (a b : V3) (r : ℝ) : cross3 a (r • b) = r • cross3 a b := by
  ext i; fin_cases i <;> simp <;> ring
theorem inner_cross3_self (a b : V3) : ⟪cross3 a b, b⟫ = 0 := by
  rw [inner3]; simp; ring
/-- **Proved.** Lagrange: `|a×b|² = |a|²|b|² − (a·b)²`. -/
theorem norm_cross3_sq (a b : V3) : ‖cross3 a b‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2 := by
  rw [normsq3, normsq3, normsq3, inner3]; simp; ring
theorem norm_cross3_le (a b : V3) : ‖cross3 a b‖ ≤ ‖a‖ * ‖b‖ := by
  have h := norm_cross3_sq a b
  have : ‖cross3 a b‖ ^ 2 ≤ (‖a‖ * ‖b‖) ^ 2 := by nlinarith [sq_nonneg ⟪a, b⟫]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 this
/-- **Proved.** Triple-product rotation `(a×b)·c = a·(b×c)`. -/
theorem inner_cross3_rot (a b c : V3) : ⟪cross3 a b, c⟫ = ⟪a, cross3 b c⟫ := by
  rw [inner3, inner3]; simp; ring

/-- **Proved.** `‖(I − τ⊗τ) v‖ ≤ ‖v‖` for unit `τ`. -/
theorem norm_perpPart_le {τ : V3} (hτ : ‖τ‖ = 1) (v : V3) : ‖perpPart τ v‖ ≤ ‖v‖ := by
  have hsplit := strain_split τ v
  have horth : ⟪perpPart τ v, ⟪τ, v⟫ • τ⟫ = 0 := by
    rw [inner_smul_right, real_inner_comm τ, inner_perpPart hτ, mul_zero]
  have h := norm_add_sq_real (perpPart τ v) (⟪τ, v⟫ • τ)
  rw [← hsplit, horth] at h
  nlinarith [norm_nonneg (perpPart τ v), norm_nonneg v, sq_nonneg ‖⟪τ, v⟫ • τ‖]

theorem perpPart_sub (t v w : V3) : perpPart t (v - w) = perpPart t v - perpPart t w := by
  simp only [perpPart, inner_sub_right, sub_smul]; abel

/-- **Proved.** `‖(I−τ⊗τ)ξ‖² = 1 − (τ·ξ)² = sin²∠(τ,ξ)` for unit `τ, ξ`. -/
theorem norm_perpPart_sq {τ ξ : V3} (hτ : ‖τ‖ = 1) (hξ : ‖ξ‖ = 1) :
    ‖perpPart τ ξ‖ ^ 2 = 1 - ⟪τ, ξ⟫ ^ 2 := by
  have hsplit := strain_split τ ξ
  have horth : ⟪perpPart τ ξ, ⟪τ, ξ⟫ • τ⟫ = 0 := by
    rw [inner_smul_right, real_inner_comm τ, inner_perpPart hτ, mul_zero]
  have h := norm_add_sq_real (perpPart τ ξ) (⟪τ, ξ⟫ • τ)
  rw [← hsplit, horth, norm_smul, hτ, hξ, Real.norm_eq_abs, mul_one, sq_abs] at h
  linarith

/-- Coined. Constantin's strain kernel applied to `τ`: for the Biot–Savart strain
`S(x) = PV∫ σ(ŷ)[ω(x+y)] dy/|y|³`, `σ(ŷ)[ξ] τ = (ŷ·τ)(ŷ×ξ) + ((ŷ×ξ)·τ) ŷ` (up to `3/8π`). -/
def csKernel (y τ ξ : V3) : V3 := ⟪y, τ⟫ • cross3 y ξ + ⟪cross3 y ξ, τ⟫ • y

/-- Coined. Bending kernel `(I − τ⊗τ) σ(ŷ)[ξ] τ`. -/
def bendKernel (y τ ξ : V3) : V3 := perpPart τ (csKernel y τ ξ)

theorem csKernel_add (y τ a b : V3) : csKernel y τ (a + b) = csKernel y τ a + csKernel y τ b := by
  simp only [csKernel, cross3_add, inner_add_left, add_smul, smul_add]; abel
theorem csKernel_smul (y τ a : V3) (r : ℝ) : csKernel y τ (r • a) = r • csKernel y τ a := by
  simp only [csKernel, cross3_smul, inner_smul_left, smul_smul, RCLike.conj_to_real, smul_add]
  rw [mul_comm]
theorem bendKernel_add (y τ a b : V3) :
    bendKernel y τ (a + b) = bendKernel y τ a + bendKernel y τ b := by
  simp only [bendKernel, csKernel_add, perpPart_add]
theorem bendKernel_smul (y τ a : V3) (r : ℝ) :
    bendKernel y τ (r • a) = r • bendKernel y τ a := by
  simp only [bendKernel, csKernel_smul, perpPart_smul]

/-- **Proved.** Stretching kernel (Constantin): `τ·σ(ŷ)[ξ]τ = 2 (ŷ·τ) det(ŷ, ξ, τ)`. -/
theorem stretch_csKernel (y τ ξ : V3) :
    ⟪τ, csKernel y τ ξ⟫ = 2 * ⟪y, τ⟫ * ⟪cross3 y ξ, τ⟫ := by
  simp only [csKernel, inner_add_right, inner_smul_right, real_inner_comm τ y,
    real_inner_comm τ (cross3 y ξ)]
  ring

/-- **Proved.** The stretching kernel vanishes for aligned directions and is bounded by
`2 sin∠(τ, ξ)`: `|τ·σ(ŷ)[ξ]τ| ≤ 2 ‖τ × ξ‖`. -/
theorem stretch_csKernel_aligned (y τ : V3) :
    ⟪τ, csKernel y τ τ⟫ = 0 := by
  rw [stretch_csKernel, inner_cross3_self, mul_zero]

theorem abs_stretch_csKernel_le {y τ : V3} (hy : ‖y‖ = 1) (hτ : ‖τ‖ = 1) (ξ : V3) :
    |⟪τ, csKernel y τ ξ⟫| ≤ 2 * ‖cross3 ξ τ‖ := by
  rw [stretch_csKernel, inner_cross3_rot]
  have h1 : |⟪y, τ⟫| ≤ 1 := by
    simpa [hy, hτ] using abs_real_inner_le_norm y τ
  have h2 : |⟪y, cross3 ξ τ⟫| ≤ ‖cross3 ξ τ‖ := by
    simpa [hy] using abs_real_inner_le_norm y (cross3 ξ τ)
  rw [abs_mul, abs_mul]
  norm_num
  nlinarith [abs_nonneg ⟪y, τ⟫, abs_nonneg ⟪y, cross3 ξ τ⟫]

/-- **Proved.** The bending kernel does **not** vanish for aligned directions:
`(I−τ⊗τ)σ(ŷ)[τ]τ = (ŷ·τ)(ŷ×τ)`. -/
theorem bendKernel_aligned (y τ : V3) :
    bendKernel y τ τ = ⟪y, τ⟫ • cross3 y τ := by
  have h1 : ⟪τ, cross3 y τ⟫ = 0 := by rw [real_inner_comm, inner_cross3_self]
  have h0 : ⟪τ, ⟪y, τ⟫ • cross3 y τ⟫ = 0 := by
    rw [inner_smul_right, h1, mul_zero]
  simp [bendKernel, csKernel, inner_cross3_self, perpPart, h0]

/-- **Proved.** `‖σ(ŷ)[d]τ‖ ≤ 2‖d‖` for unit `ŷ, τ`. -/
theorem norm_csKernel_le {y τ : V3} (hy : ‖y‖ = 1) (hτ : ‖τ‖ = 1) (d : V3) :
    ‖csKernel y τ d‖ ≤ 2 * ‖d‖ := by
  have hc : ‖cross3 y d‖ ≤ ‖d‖ := by simpa [hy] using norm_cross3_le y d
  have h1 : |⟪y, τ⟫| ≤ 1 := by simpa [hy, hτ] using abs_real_inner_le_norm y τ
  have h2 : |⟪cross3 y d, τ⟫| ≤ ‖d‖ := by
    have := abs_real_inner_le_norm (cross3 y d) τ
    rw [hτ, mul_one] at this; linarith
  calc ‖csKernel y τ d‖ ≤ ‖⟪y, τ⟫ • cross3 y d‖ + ‖⟪cross3 y d, τ⟫ • y‖ := norm_add_le _ _
    _ = |⟪y, τ⟫| * ‖cross3 y d‖ + |⟪cross3 y d, τ⟫| := by
        rw [norm_smul, norm_smul, hy, Real.norm_eq_abs, Real.norm_eq_abs, mul_one]
    _ ≤ 1 * ‖d‖ + ‖d‖ := by
        gcongr
    _ = 2 * ‖d‖ := by ring

/-- **Proved.** Exact split of the bending kernel by the angle between `τ` and `ξ`:
`bendKernel ŷ τ ξ = (τ·ξ)(ŷ·τ)(ŷ×τ) + bendKernel ŷ τ ((I−τ⊗τ)ξ)`, and the remainder is at most
`2 sin∠(τ,ξ)`. The first (non-depleted) term carries `cos∠`. -/
theorem bendKernel_split (y τ ξ : V3) :
    bendKernel y τ ξ = ⟪τ, ξ⟫ • (⟪y, τ⟫ • cross3 y τ) + bendKernel y τ (perpPart τ ξ) := by
  conv_lhs => rw [strain_split τ ξ]
  rw [add_comm (perpPart τ ξ), bendKernel_add, bendKernel_smul, bendKernel_aligned]

theorem norm_bendKernel_perp_le {y τ : V3} (hy : ‖y‖ = 1) (hτ : ‖τ‖ = 1) (ξ : V3) :
    ‖bendKernel y τ (perpPart τ ξ)‖ ≤ 2 * ‖perpPart τ ξ‖ :=
  (norm_perpPart_le hτ _).trans (norm_csKernel_le hy hτ _)

/-- **Proved.** Lipschitz form: `‖bendKernel ŷ τ ξ − bendKernel ŷ τ τ‖ ≤ 2‖ξ − τ‖`. -/
theorem norm_bendKernel_sub_aligned_le {y τ : V3} (hy : ‖y‖ = 1) (hτ : ‖τ‖ = 1) (ξ : V3) :
    ‖bendKernel y τ ξ - bendKernel y τ τ‖ ≤ 2 * ‖ξ - τ‖ := by
  have : bendKernel y τ ξ - bendKernel y τ τ = bendKernel y τ (ξ - τ) := by
    rw [sub_eq_add_neg ξ, bendKernel_add, ← neg_one_smul ℝ τ, bendKernel_smul]
    simp [sub_eq_add_neg]
  rw [this]
  exact (norm_perpPart_le hτ _).trans (norm_csKernel_le hy hτ _)

/-- **Proved.** Discretized (quadrature) model of the principal-value integral: for weights
`w n` (standing for `|ω(x+yₙ)| ΔV/|yₙ|³`), unit `ŷₙ` and unit directions `ξₙ = τ(x+yₙ)`,
the bending sum is bounded by its non-depleted aligned part plus `2 Σ |wₙ| sin∠(τ, ξₙ)`. -/
theorem norm_bending_sum_le {ι : Type*} (s : Finset ι) (w : ι → ℝ) (y ξ : ι → V3) {τ : V3}
    (hy : ∀ n, ‖y n‖ = 1) (hτ : ‖τ‖ = 1) :
    ‖∑ n ∈ s, w n • bendKernel (y n) τ (ξ n)‖ ≤
      ‖∑ n ∈ s, (w n * ⟪τ, ξ n⟫) • (⟪y n, τ⟫ • cross3 (y n) τ)‖ +
        2 * ∑ n ∈ s, |w n| * ‖perpPart τ (ξ n)‖ := by
  have hs : ∑ n ∈ s, w n • bendKernel (y n) τ (ξ n) =
      ∑ n ∈ s, (w n * ⟪τ, ξ n⟫) • (⟪y n, τ⟫ • cross3 (y n) τ) +
        ∑ n ∈ s, w n • bendKernel (y n) τ (perpPart τ (ξ n)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [bendKernel_split, smul_add, smul_smul]
  rw [hs]
  refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [norm_smul, Real.norm_eq_abs]
  nlinarith [norm_bendKernel_perp_le (hy n) hτ (ξ n), abs_nonneg (w n)]

end PeriodicNSContinuation
