import Mathlib

/-!
# A uniform bound for the sine partial sums `∑_{k≤n} sin(kx)/k`

Elementary Fejér–Jackson–Gronwall-type bound with the explicit constant `3`
(the sharp constant is `Si(π) ≈ 1.852`, not formalized). Proof: split at `m = ⌊1/|sin(x/2)|⌋`,
bound the head by `|sin(kx)| ≤ 2k|sin(x/2)|` and the tail by Abel summation with the
telescoped Dirichlet sum `2 sin(x/2) ∑ sin(kx) = cos − cos`.
-/

open Finset

namespace PeriodicNSContinuation.SineSumBound

/-- Abel's inequality. -/
theorem abel_le (a b : ℕ → ℝ) (B : ℝ) (hb : Antitone b) (hb0 : ∀ k, 0 ≤ b k)
    (hT : ∀ j, |∑ k ∈ range j, a k| ≤ B) (n : ℕ) :
    |∑ k ∈ range n, a k * b k| ≤ B * b 0 := by
  set T : ℕ → ℝ := fun j => ∑ k ∈ range j, a k
  have key : ∀ n, ∑ k ∈ range n, a k * b k =
      T n * b n + ∑ k ∈ range n, T (k+1) * (b k - b (k+1)) := by
    intro n; induction n with
    | zero => simp [T]
    | succ n ih =>
      rw [sum_range_succ, ih, sum_range_succ]; simp only [T, sum_range_succ]; ring
  rw [key]
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hT 0)
  have tel : ∑ k ∈ range n, (b k - b (k+1)) = b 0 - b n := by
    rw [sum_range_sub']
  calc |T n * b n + ∑ k ∈ range n, T (k+1) * (b k - b (k+1))|
      ≤ |T n * b n| + ∑ k ∈ range n, |T (k+1) * (b k - b (k+1))| :=
        (abs_add_le _ _).trans (add_le_add le_rfl (abs_sum_le_sum_abs _ _))
    _ ≤ B * b n + ∑ k ∈ range n, B * (b k - b (k+1)) := by
        gcongr with k
        · rw [abs_mul, abs_of_nonneg (hb0 n)]; exact mul_le_mul_of_nonneg_right (hT n) (hb0 n)
        · rw [abs_mul, abs_of_nonneg (sub_nonneg.2 (hb (Nat.le_succ k)))]
          exact mul_le_mul_of_nonneg_right (hT _) (sub_nonneg.2 (hb (Nat.le_succ k)))
    _ = B * b 0 := by rw [← mul_sum, tel]; ring

/-- Telescoped Dirichlet sum. -/
lemma dirichlet_tel (x : ℝ) (p r : ℕ) :
    2 * Real.sin (x/2) * ∑ k ∈ range r, Real.sin (((p + k : ℕ) : ℝ) * x) =
      Real.cos (((p:ℝ) - 1/2) * x) - Real.cos ((((p + r : ℕ) : ℝ) - 1/2) * x) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [sum_range_succ, mul_add, ih]
    have : 2 * Real.sin (x/2) * Real.sin (((p + r : ℕ) : ℝ) * x) =
        Real.cos ((((p + r : ℕ) : ℝ) - 1/2) * x) - Real.cos ((((p + (r+1) : ℕ) : ℝ) - 1/2) * x) := by
      have e1 : (((p + r : ℕ) : ℝ) - 1/2) * x = ((p + r : ℕ) : ℝ) * x - x/2 := by ring
      have e2 : (((p + (r+1) : ℕ) : ℝ) - 1/2) * x = ((p + r : ℕ) : ℝ) * x + x/2 := by push_cast; ring
      rw [e1, e2, Real.cos_sub, Real.cos_add]; ring
    rw [this]; ring

lemma abs_dirichlet_le (x : ℝ) (p r : ℕ) :
    |Real.sin (x/2)| * |∑ k ∈ range r, Real.sin (((p + k : ℕ) : ℝ) * x)| ≤ 1 := by
  have h := congrArg abs (dirichlet_tel x p r)
  rw [abs_mul, abs_mul, abs_two, mul_assoc] at h
  have hc : |Real.cos (((p:ℝ) - 1/2) * x) - Real.cos ((((p + r : ℕ) : ℝ) - 1/2) * x)| ≤ 2 := by
    have h1 := abs_le.1 (Real.abs_cos_le_one (((p:ℝ) - 1/2) * x))
    have h2 := abs_le.1 (Real.abs_cos_le_one ((((p + r : ℕ) : ℝ) - 1/2) * x))
    exact abs_le.2 ⟨by linarith, by linarith⟩
  linarith

lemma abs_sin_nat_mul_le (x : ℝ) (k : ℕ) : |Real.sin (k * x)| ≤ k * |Real.sin x| := by
  induction k with
  | zero => simp
  | succ k ih =>
    push_cast
    rw [add_mul, one_mul, Real.sin_add]
    calc _ ≤ |Real.sin (k*x) * Real.cos x| + |Real.cos (k*x) * Real.sin x| := abs_add_le _ _
      _ ≤ (k * |Real.sin x|) * 1 + 1 * |Real.sin x| := by
          rw [abs_mul, abs_mul]
          gcongr
          · exact Real.abs_cos_le_one _
          · exact Real.abs_cos_le_one _
      _ = _ := by ring

lemma abs_sin_le_two_half (x : ℝ) : |Real.sin x| ≤ 2 * |Real.sin (x/2)| := by
  have : Real.sin x = 2 * Real.sin (x/2) * Real.cos (x/2) := by
    rw [← Real.sin_two_mul]; ring_nf
  rw [this, abs_mul, abs_mul]
  have := Real.abs_cos_le_one (x/2)
  have := abs_nonneg (Real.sin (x/2))
  norm_num; nlinarith

/-- `g n x = ∑_{k<n} sin((k+1)x)/(k+1)`. -/
noncomputable def g (n : ℕ) (x : ℝ) : ℝ := ∑ k ∈ range n, Real.sin (((k+1 : ℕ) : ℝ) * x) / ((k+1 : ℕ) : ℝ)

lemma g_succ (n : ℕ) (x : ℝ) :
    g (n+1) x = g n x + Real.sin (((n+1 : ℕ) : ℝ) * x) / ((n+1 : ℕ) : ℝ) := by
  simp only [g, sum_range_succ]

lemma head_le (n : ℕ) (x : ℝ) : |g n x| ≤ 2 * n * |Real.sin (x/2)| := by
  unfold g
  calc _ ≤ ∑ k ∈ range n, |Real.sin (((k+1 : ℕ) : ℝ) * x) / ((k+1 : ℕ) : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range n, 2 * |Real.sin (x/2)| := by
        apply sum_le_sum; intro k _
        have hk : (0:ℝ) < ((k+1 : ℕ) : ℝ) := by positivity
        rw [abs_div, abs_of_pos hk, div_le_iff₀ hk]
        have := abs_sin_nat_mul_le x (k+1)
        have := abs_sin_le_two_half x
        nlinarith
    _ = _ := by simp; ring

/-- **Uniform bound** `|∑_{k≤n} sin(kx)/k| ≤ 3` for all `n` and `x`. -/
theorem abs_g_le_three (n : ℕ) (x : ℝ) : |g n x| ≤ 3 := by
  set s := |Real.sin (x/2)|
  rcases eq_or_lt_of_le (abs_nonneg (Real.sin (x/2))) with hs | hs
  · have := head_le n x; rw [← hs] at this; linarith
  set m := ⌊1/s⌋₊
  have hm1 : (m:ℝ) * s ≤ 1 := by
    have := Nat.floor_le (a := 1/s) (by positivity)
    rwa [le_div_iff₀ hs] at this
  have hm2 : 1 ≤ ((m:ℝ) + 1) * s := by
    have := Nat.lt_floor_add_one (1/s)
    rw [div_lt_iff₀ hs] at this; linarith
  rcases le_or_gt n m with hn | hn
  · have := head_le n x
    have : (n:ℝ) * s ≤ 1 := le_trans (by gcongr) hm1
    linarith
  obtain ⟨r, rfl⟩ : ∃ r, n = m + r := ⟨n - m, by omega⟩
  have split : g (m + r) x = g m x + ∑ k ∈ range r,
      Real.sin (((m + 1 + k : ℕ) : ℝ) * x) * (1 / ((m + 1 + k : ℕ) : ℝ)) := by
    unfold g; rw [sum_range_add]; congr 1; apply sum_congr rfl; intro k _
    rw [show m + k + 1 = m + 1 + k by omega]; ring
  have hhead : |g m x| ≤ 2 := by have := head_le m x; linarith
  have htail := abel_le (fun k => Real.sin (((m + 1 + k : ℕ) : ℝ) * x))
    (fun k => 1 / ((m + 1 + k : ℕ) : ℝ)) (1/s)
    (by intro i j hij; simp only; gcongr)
    (fun k => by positivity)
    (fun j => by
      have := abs_dirichlet_le x (m+1) j
      rw [le_div_iff₀ hs]; linarith [mul_comm s |∑ k ∈ range j, Real.sin (((m + 1 + k : ℕ) : ℝ) * x)|]) r
  have hb0 : 1 / s * (1 / ((m + 1 + 0 : ℕ) : ℝ)) ≤ 1 := by
    push_cast
    rw [div_mul_div_comm, one_mul, div_le_one (by positivity)]; linarith
  rw [split]
  calc _ ≤ |g m x| + |∑ k ∈ range r, Real.sin (((m + 1 + k : ℕ) : ℝ) * x) * (1 / ((m + 1 + k : ℕ) : ℝ))| :=
        abs_add_le _ _
    _ ≤ 2 + 1 := add_le_add hhead (htail.trans hb0)
    _ = 3 := by norm_num

/-- Odd partial sums: `∑_{i<N} sin((2i+1)x)/(2i+1) = g (2N) x - ½ g N (2x)`. -/
lemma odd_sum_eq (N : ℕ) (x : ℝ) :
    ∑ i ∈ range N, Real.sin ((2*(i:ℝ)+1) * x) / (2*(i:ℝ)+1) = g (2*N) x - 1/2 * g N (2*x) := by
  induction N with
  | zero => simp [g]
  | succ N ih =>
    rw [sum_range_succ, ih, show 2*(N+1) = 2*N + 1 + 1 by ring, g_succ, g_succ, g_succ]
    push_cast
    have h : (2:ℝ)*N + 1 + 1 ≠ 0 := by positivity
    have h' : (N:ℝ) + 1 ≠ 0 := by positivity
    rw [show ((2:ℝ)*N + 1 + 1) * x = ((N:ℝ)+1) * (2*x) by ring,
      show (2:ℝ)*N + 1 + 1 = 2 * ((N:ℝ)+1) by ring]
    field_simp; ring

/-- `|∑_{i<N} sin((2i+1)x)/(2i+1)| ≤ 9/2`. -/
theorem abs_odd_sum_le (N : ℕ) (x : ℝ) :
    |∑ i ∈ range N, Real.sin ((2*(i:ℝ)+1) * x) / (2*(i:ℝ)+1)| ≤ 9/2 := by
  rw [odd_sum_eq]
  have := abs_g_le_three (2*N) x; have := abs_g_le_three N (2*x)
  calc _ ≤ |g (2*N) x| + |1/2 * g N (2*x)| := abs_sub _ _
    _ ≤ 3 + 1/2 * 3 := by rw [abs_mul]; norm_num; linarith
    _ = 9/2 := by norm_num

end PeriodicNSContinuation.SineSumBound
