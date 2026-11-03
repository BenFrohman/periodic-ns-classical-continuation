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

/-- `log (n+1) ≤ ∑_{i<n} 1/(i+1)`. -/
lemma log_succ_le_harmonicSum (n : ℕ) : Real.log ((n:ℝ)+1) ≤ ∑ i ∈ range n, (1 / ((i:ℝ)+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have h1 : (0:ℝ) < (n:ℝ)+1 := by positivity
    have hstep : Real.log (((n+1:ℕ):ℝ)+1) - Real.log ((n:ℝ)+1) ≤ 1 / ((n:ℝ)+1) := by
      rw [← Real.log_div (by positivity) h1.ne']
      have := Real.log_le_sub_one_of_pos (x := (((n+1:ℕ):ℝ)+1) / ((n:ℝ)+1)) (by positivity)
      have he : (((n+1:ℕ):ℝ)+1) / ((n:ℝ)+1) - 1 = 1 / ((n:ℝ)+1) := by
        push_cast; field_simp; ring
      linarith
    linarith

/-- **Explicit, for every `n`:** `bcSum n ≥ (1/8) log (n+1)`. -/
theorem bcSum_ge_log (n : ℕ) : (1/8) * Real.log ((n:ℝ)+1) ≤ bcSum n :=
  le_trans (by gcongr; exact log_succ_le_harmonicSum n) (bcSum_lb n)

/-- **Explicit strain lower bound at the origin, every odd `K = 2n-1 ≥ 1`:**
`(16/π²) · bcSum n ≥ (1/π²) log K` (uses `(K+1)/2 ≥ √K`). Combined with the (classical, not
formalized here) identity `S₁₁(0) = (16/π²) bcSum n`, this gives `‖S_K‖_∞ ≥ (1/π²) log K`. -/
theorem originStrain_ge_log (n : ℕ) (hn : 1 ≤ n) :
    (1 / Real.pi^2) * Real.log (2*(n:ℝ)-1) ≤ (16 / Real.pi^2) * bcSum n := by
  have hK : (1:ℝ) ≤ 2*(n:ℝ)-1 := by
    have : (1:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hK0 : (0:ℝ) < 2*(n:ℝ)-1 := by linarith
  -- log K ≤ 2 log n ≤ 2 log (n+1)
  have hlog : Real.log (2*(n:ℝ)-1) ≤ 2 * Real.log ((n:ℝ)+1) := by
    rw [← Real.log_rpow (by positivity)]
    apply Real.log_le_log hK0
    have : (((n:ℝ)+1) ^ (2:ℝ)) = ((n:ℝ)+1)^2 := by norm_cast
    rw [this]; nlinarith
  have hb := bcSum_ge_log n
  have hpi : 0 < Real.pi^2 := by positivity
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hpi]
  linarith

end PeriodicNSContinuation.StrainLinf
