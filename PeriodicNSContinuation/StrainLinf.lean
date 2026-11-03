import Mathlib

/-!
# `PeriodicStrainLinfBound`: the Bahouri–Chemin obstruction (arithmetic core)

Family on `T³` (z-independent, `u₃ = 0`): `ω_K = f_K(x) f_K(y) e_z`, with `f_K` the Dirichlet partial
sum of `sgn(sin x)`. Then `‖ω_K‖_∞ → ((2/π) Si π)² ≈ 1.39` (Gibbs; classical, checked numerically),
and the strain at the origin is `S₁₁(0) = (16/π²) · bcSum n`, `n = (K+1)/2` (Fourier computation,
checked numerically in `paper/strain_linf/`). This file proves only the arithmetic core:
`bcSum` is unbounded. Not formalized here: the Fourier identity, the Gibbs bound, and the local
existence that would turn the family into a Lean refutation of `PeriodicStrainLinfBound`.
-/

open Finset Filter Topology

namespace PeriodicNSContinuation.StrainLinf

/-- Partial double sum at the origin: `∑_{i,j<n} 1/((2i+1)²+(2j+1)²)`. -/
noncomputable def bcSum (n : ℕ) : ℝ :=
  ∑ i ∈ range n, ∑ j ∈ range n, 1 / (((2*i+1:ℕ):ℝ)^2 + ((2*j+1:ℕ):ℝ)^2)

lemma row_lb (n i : ℕ) (hi : i < n) :
    1 / (8 * ((i:ℝ)+1)) ≤ ∑ j ∈ range n, 1 / (((2*i+1:ℕ):ℝ)^2 + ((2*j+1:ℕ):ℝ)^2) := by
  have hsub : range (i+1) ⊆ range n := range_mono (by omega)
  calc 1 / (8 * ((i:ℝ)+1)) ≤ ∑ j ∈ range (i+1), 1 / (((2*i+1:ℕ):ℝ)^2 + ((2*j+1:ℕ):ℝ)^2) := by
        have : ∀ j ∈ range (i+1), 1 / (8 * ((i:ℝ)+1)^2) ≤ 1 / (((2*i+1:ℕ):ℝ)^2 + ((2*j+1:ℕ):ℝ)^2) := by
          intro j hj
          have hj' : (j:ℝ) ≤ i := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hj)
          apply one_div_le_one_div_of_le (by positivity)
          push_cast; nlinarith
        calc 1 / (8 * ((i:ℝ)+1)) = ∑ j ∈ range (i+1), 1 / (8 * ((i:ℝ)+1)^2) := by
              rw [sum_const, card_range, nsmul_eq_mul]; push_cast; field_simp
          _ ≤ _ := sum_le_sum this
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

lemma bcSum_lb (n : ℕ) : (1/8) * ∑ i ∈ range n, (1 / ((i:ℝ)+1)) ≤ bcSum n := by
  rw [mul_sum]; unfold bcSum
  exact sum_le_sum fun i hi => by
    have := row_lb n i (mem_range.mp hi); rw [show (1:ℝ)/8 * (1/((i:ℝ)+1)) = 1/(8*((i:ℝ)+1)) by field_simp]; exact this

/-- The Bahouri–Chemin origin strain sum is unbounded (it grows like `(π/8) log n`). -/
theorem bcSum_unbounded : Tendsto bcSum atTop atTop := by
  have h := Real.tendsto_sum_range_one_div_nat_succ_atTop
  exact tendsto_atTop_mono bcSum_lb (Tendsto.const_mul_atTop (by norm_num) h)

end PeriodicNSContinuation.StrainLinf
