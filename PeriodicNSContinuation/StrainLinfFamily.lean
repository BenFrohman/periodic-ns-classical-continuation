import PeriodicNSContinuation.BendingRate
import PeriodicNSContinuation.StrainLinf

open Finset Filter Topology FeffermanClayNS NavierStokes3D
open scoped RealInnerProductSpace

namespace PeriodicNSContinuation.StrainLinfFamily

/-- odd frequency `2i+1`. -/
def kk (i : ℕ) : ℝ := 2 * (i:ℝ) + 1

noncomputable def U0 (N : ℕ) (a b : ℝ) : ℝ :=
  ∑ i ∈ range N, ∑ j ∈ range N, (8 / Real.pi^3) / (kk i * (kk i ^ 2 + kk j ^ 2)) *
    (Real.sin (2 * Real.pi * kk i * a) * Real.cos (2 * Real.pi * kk j * b))

noncomputable def U1 (N : ℕ) (a b : ℝ) : ℝ :=
  -∑ i ∈ range N, ∑ j ∈ range N, (8 / Real.pi^3) / (kk j * (kk i ^ 2 + kk j ^ 2)) *
    (Real.cos (2 * Real.pi * kk i * a) * Real.sin (2 * Real.pi * kk j * b))

noncomputable def uK (N : ℕ) : VelocityField := fun x => !₂[U0 N (x 0) (x 1), U1 N (x 0) (x 1), 0]

example (N : ℕ) (x : T3) : uK N x 0 = U0 N (x 0) (x 1) := by simp [uK]
example (N : ℕ) (x : T3) : uK N x 2 = 0 := by simp [uK]

lemma contDiff_U0 (N : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => U0 N p.1 p.2) := by
  unfold U0; fun_prop

lemma contDiff_U1 (N : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => U1 N p.1 p.2) := by
  unfold U1; fun_prop

lemma contDiff_coord (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x : T3 => x i) := by fun_prop

lemma contDiff_uK (N : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (uK N) := by
  rw [contDiff_euclidean]
  intro i
  have h0 : ContDiff ℝ (⊤ : ℕ∞) (fun x : T3 => U0 N (x 0) (x 1)) :=
    by unfold U0; fun_prop
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun x : T3 => U1 N (x 0) (x 1)) :=
    by unfold U1; fun_prop
  fin_cases i
  · simpa [uK] using h0
  · simpa [uK] using h1
  · simp [uK]; exact contDiff_const

/-- Partial derivative as a line derivative. -/
lemma fderiv_apply_eq_deriv {f : T3 → ℝ} {x : T3} (hf : DifferentiableAt ℝ f x) (v : T3) :
    fderiv ℝ f x v = deriv (fun t : ℝ => f (x + t • v)) 0 := by
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  have hf' : HasFDerivAt f (fderiv ℝ f x) (x + (0:ℝ) • v) := by simpa using hf.hasFDerivAt
  have := hf'.comp_hasDerivAt (0:ℝ) hl
  exact (this.deriv).symm

noncomputable def cc (i j : ℕ) : ℝ := (8 / Real.pi^3) / (kk i * (kk i ^ 2 + kk j ^ 2))
noncomputable def dd (i j : ℕ) : ℝ := (8 / Real.pi^3) / (kk j * (kk i ^ 2 + kk j ^ 2))

lemma U0_eq (N : ℕ) (a b : ℝ) : U0 N a b = ∑ i ∈ range N, ∑ j ∈ range N, cc i j *
    (Real.sin (2 * Real.pi * kk i * a) * Real.cos (2 * Real.pi * kk j * b)) := rfl
lemma U1_eq (N : ℕ) (a b : ℝ) : U1 N a b = -∑ i ∈ range N, ∑ j ∈ range N, dd i j *
    (Real.cos (2 * Real.pi * kk i * a) * Real.sin (2 * Real.pi * kk j * b)) := rfl

lemma hd_sin (c a : ℝ) : HasDerivAt (fun a => Real.sin (c * a)) (Real.cos (c * a) * c) a := by
  simpa using (Real.hasDerivAt_sin (c*a)).comp a ((hasDerivAt_id a).const_mul c)
lemma hd_cos (c a : ℝ) : HasDerivAt (fun a => Real.cos (c * a)) (-Real.sin (c * a) * c) a := by
  simpa using (Real.hasDerivAt_cos (c*a)).comp a ((hasDerivAt_id a).const_mul c)

noncomputable def D0U0 (N : ℕ) (a b : ℝ) : ℝ := ∑ i ∈ range N, ∑ j ∈ range N, cc i j *
    ((Real.cos (2 * Real.pi * kk i * a) * (2 * Real.pi * kk i)) * Real.cos (2 * Real.pi * kk j * b))
noncomputable def D1U0 (N : ℕ) (a b : ℝ) : ℝ := ∑ i ∈ range N, ∑ j ∈ range N, cc i j *
    (Real.sin (2 * Real.pi * kk i * a) * (-Real.sin (2 * Real.pi * kk j * b) * (2 * Real.pi * kk j)))
noncomputable def D0U1 (N : ℕ) (a b : ℝ) : ℝ := -∑ i ∈ range N, ∑ j ∈ range N, dd i j *
    ((-Real.sin (2 * Real.pi * kk i * a) * (2 * Real.pi * kk i)) * Real.sin (2 * Real.pi * kk j * b))
noncomputable def D1U1 (N : ℕ) (a b : ℝ) : ℝ := -∑ i ∈ range N, ∑ j ∈ range N, dd i j *
    (Real.cos (2 * Real.pi * kk i * a) * (Real.cos (2 * Real.pi * kk j * b) * (2 * Real.pi * kk j)))

lemma hasDerivAt_U0_a (N : ℕ) (a b : ℝ) : HasDerivAt (fun a => U0 N a b) (D0U0 N a b) a := by
  simp only [U0_eq, D0U0]
  apply HasDerivAt.fun_sum; intro i _; apply HasDerivAt.fun_sum; intro j _
  exact ((hd_sin _ a).mul_const _).const_mul _
lemma hasDerivAt_U0_b (N : ℕ) (a b : ℝ) : HasDerivAt (fun b => U0 N a b) (D1U0 N a b) b := by
  simp only [U0_eq, D1U0]
  apply HasDerivAt.fun_sum; intro i _; apply HasDerivAt.fun_sum; intro j _
  exact ((hd_cos _ b).const_mul _).const_mul _
lemma hasDerivAt_U1_a (N : ℕ) (a b : ℝ) : HasDerivAt (fun a => U1 N a b) (D0U1 N a b) a := by
  simp only [U1_eq, D0U1]
  apply HasDerivAt.neg
  apply HasDerivAt.fun_sum; intro i _; apply HasDerivAt.fun_sum; intro j _
  exact ((hd_cos _ a).mul_const _).const_mul _
lemma hasDerivAt_U1_b (N : ℕ) (a b : ℝ) : HasDerivAt (fun b => U1 N a b) (D1U1 N a b) b := by
  simp only [U1_eq, D1U1]
  apply HasDerivAt.neg
  apply HasDerivAt.fun_sum; intro i _; apply HasDerivAt.fun_sum; intro j _
  exact ((hd_sin _ b).const_mul _).const_mul _

lemma differentiableAt_comp (N : ℕ) (c : Fin 3) (x : T3) :
    DifferentiableAt ℝ (fun y => uK N y c) x := by
  have h := (contDiff_uK N).differentiable (by simp)
  exact ((EuclideanSpace.proj c : T3 →L[ℝ] ℝ).differentiable.comp h) x

lemma line0 (x : T3) (t : ℝ) : (x + t • EuclideanSpace.single (0:Fin 3) (1:ℝ)) 0 = x 0 + t ∧
    (x + t • EuclideanSpace.single (0:Fin 3) (1:ℝ)) 1 = x 1 := by simp
lemma line1 (x : T3) (t : ℝ) : (x + t • EuclideanSpace.single (1:Fin 3) (1:ℝ)) 0 = x 0 ∧
    (x + t • EuclideanSpace.single (1:Fin 3) (1:ℝ)) 1 = x 1 + t := by simp
lemma line2 (x : T3) (t : ℝ) : (x + t • EuclideanSpace.single (2:Fin 3) (1:ℝ)) 0 = x 0 ∧
    (x + t • EuclideanSpace.single (2:Fin 3) (1:ℝ)) 1 = x 1 := by simp

lemma dc00 (N : ℕ) (x : T3) : directionalCoord (uK N) 0 0 x = D0U0 N (x 0) (x 1) := by
  unfold directionalCoord
  rw [fderiv_apply_eq_deriv (differentiableAt_comp N 0 x)]
  simp only [uK, line0]
  simpa using ((hasDerivAt_U0_a N (x 0 + 0) (x 1)).comp_const_add (x 0) 0).deriv
lemma dc01 (N : ℕ) (x : T3) : directionalCoord (uK N) 0 1 x = D1U0 N (x 0) (x 1) := by
  unfold directionalCoord
  rw [fderiv_apply_eq_deriv (differentiableAt_comp N 0 x)]
  simp only [uK, line1]
  simpa using ((hasDerivAt_U0_b N (x 0) (x 1 + 0)).comp_const_add (x 1) 0).deriv
lemma dc10 (N : ℕ) (x : T3) : directionalCoord (uK N) 1 0 x = D0U1 N (x 0) (x 1) := by
  unfold directionalCoord
  rw [fderiv_apply_eq_deriv (differentiableAt_comp N 1 x)]
  simp only [uK, line0]
  simpa using ((hasDerivAt_U1_a N (x 0 + 0) (x 1)).comp_const_add (x 0) 0).deriv
lemma dc11 (N : ℕ) (x : T3) : directionalCoord (uK N) 1 1 x = D1U1 N (x 0) (x 1) := by
  unfold directionalCoord
  rw [fderiv_apply_eq_deriv (differentiableAt_comp N 1 x)]
  simp only [uK, line1]
  simpa using ((hasDerivAt_U1_b N (x 0) (x 1 + 0)).comp_const_add (x 1) 0).deriv
lemma dc_2 (N : ℕ) (c : Fin 3) (x : T3) (hc : c ≠ 2) : directionalCoord (uK N) c 2 x = 0 := by
  unfold directionalCoord
  rw [fderiv_apply_eq_deriv (differentiableAt_comp N c x)]
  fin_cases c <;> simp_all [uK]
lemma dc2_ (N : ℕ) (d : Fin 3) (x : T3) : directionalCoord (uK N) 2 d x = 0 := by
  unfold directionalCoord
  rw [fderiv_apply_eq_deriv (differentiableAt_comp N 2 x)]
  simp [uK]

lemma kk_pos (i : ℕ) : 0 < kk i := by unfold kk; positivity

lemma div_uK (N : ℕ) (x : T3) : div (uK N) x = 0 := by
  have e : div (uK N) x = directionalCoord (uK N) 0 0 x + directionalCoord (uK N) 1 1 x +
      directionalCoord (uK N) 2 2 x := by
    simp [div, directionalCoord, Fin.sum_univ_three]
  rw [e, dc00, dc11, dc2_, D0U0, D1U1, add_zero, ← sub_eq_add_neg, ← sum_sub_distrib]
  apply sum_eq_zero; intro i _
  rw [← sum_sub_distrib]; apply sum_eq_zero; intro j _
  have hi := kk_pos i; have hj := kk_pos j
  simp only [cc, dd]; field_simp; ring

lemma sin_shift (c : ℕ) (a : ℝ) (m : ℤ) :
    Real.sin (2 * Real.pi * kk c * (a + m)) = Real.sin (2 * Real.pi * kk c * a) := by
  have : 2 * Real.pi * kk c * (a + m) = 2 * Real.pi * kk c * a + (((2*c+1 : ℕ) : ℤ) * m : ℤ) * (2 * Real.pi) := by
    push_cast [kk]; ring
  rw [this, Real.sin_add_int_mul_two_pi]
lemma cos_shift (c : ℕ) (a : ℝ) (m : ℤ) :
    Real.cos (2 * Real.pi * kk c * (a + m)) = Real.cos (2 * Real.pi * kk c * a) := by
  have : 2 * Real.pi * kk c * (a + m) = 2 * Real.pi * kk c * a + (((2*c+1 : ℕ) : ℤ) * m : ℤ) * (2 * Real.pi) := by
    push_cast [kk]; ring
  rw [this, Real.cos_add_int_mul_two_pi]

lemma U0_shift (N : ℕ) (a b : ℝ) (m n : ℤ) : U0 N (a + m) (b + n) = U0 N a b := by
  simp only [U0_eq, sin_shift, cos_shift]
lemma U1_shift (N : ℕ) (a b : ℝ) (m n : ℤ) : U1 N (a + m) (b + n) = U1 N a b := by
  simp only [U1_eq, sin_shift, cos_shift]

lemma periodic_uK (N : ℕ) : IsZ3Periodic (uK N) := by
  intro x k
  have h0 : (x + intVecToT3 k) 0 = x 0 + (k 0 : ℤ) := by
    simp [intVecToT3, stdBasisVec, Fin.sum_univ_three]
  have h1 : (x + intVecToT3 k) 1 = x 1 + (k 1 : ℤ) := by
    simp [intVecToT3, stdBasisVec, Fin.sum_univ_three]
  simp only [uK, h0, h1, U0_shift, U1_shift]

/-- **Milestone 1a.** `u_K` is smooth, divergence-free and `ℤ³`-periodic. -/
theorem uK_initialData (N : ℕ) : IsPeriodicSmoothInitialData (uK N) :=
  ⟨contDiff_uK N, div_uK N, periodic_uK N⟩

/-- The one-dimensional profile `F(a) = (4/π) ∑_{i<N} sin(2π(2i+1)a)/(2i+1)`. -/
noncomputable def F (N : ℕ) (a : ℝ) : ℝ :=
  ∑ i ∈ range N, (4 / Real.pi) * (Real.sin (2 * Real.pi * kk i * a) / kk i)

lemma vort_eq (N : ℕ) (x : T3) :
    vorticity (uK N) x = EuclideanSpace.single 2 (F N (x 0) * F N (x 1)) := by
  have e : D0U1 N (x 0) (x 1) - D1U0 N (x 0) (x 1) = F N (x 0) * F N (x 1) := by
    rw [F, F, sum_mul_sum, D0U1, D1U0, ← sub_eq_zero]
    simp only [← sum_neg_distrib, ← sum_sub_distrib]
    apply sum_eq_zero; intro i _; apply sum_eq_zero; intro j _
    have hi := kk_pos i; have hj := kk_pos j; have hp := Real.pi_pos
    simp only [cc, dd]; field_simp; ring
  simp [vorticity, curl, dc_2 N 1 x (by decide), dc_2 N 0 x (by decide), dc2_, dc10, dc01, e]
  ext i; fin_cases i <;> simp

lemma fderiv_coord (N : ℕ) (x v : T3) (c : Fin 3) :
    (fderiv ℝ (uK N) x v) c = fderiv ℝ (fun y => uK N y c) x v := by
  have hu := ((contDiff_uK N).differentiable (by simp) x).hasFDerivAt
  have := ((EuclideanSpace.proj c : T3 →L[ℝ] ℝ).hasFDerivAt.comp x hu).fderiv
  rw [show (fun y => uK N y c) = (EuclideanSpace.proj c : T3 →L[ℝ] ℝ) ∘ uK N from rfl, this]
  rfl

/-- The `(0,0)` strain entry equals `∂₀u₀`. -/
lemma inner_strain_e0 (N : ℕ) (x : T3) :
    ⟪EuclideanSpace.single 0 1, strainAt (uK N) x (EuclideanSpace.single 0 1)⟫ =
      D0U0 N (x 0) (x 1) := by
  rw [← dc00, directionalCoord, ← fderiv_coord]
  simp only [strainAt, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    inner_smul_right, inner_add_right, ContinuousLinearMap.adjoint_inner_right,
    real_inner_comm (fderiv ℝ (uK N) x _)]
  have h : ∀ v : T3, ⟪v, EuclideanSpace.single 0 1⟫ = v 0 := by
    intro v; simp [PiLp.inner_apply, Fin.sum_univ_three]; simp [inner]
  rw [h]; ring

/-- **Milestone 1b (Fourier identity).** `S₁₁(0) = (16/π²) · bcSum N` for the explicit family
(frequencies `2π(2i+1)`, `i < N`, i.e. `K = 2N-1`). -/
theorem strain00_origin (N : ℕ) :
    ⟪EuclideanSpace.single 0 1, strainAt (uK N) 0 (EuclideanSpace.single 0 1)⟫ =
      (16 / Real.pi ^ 2) * StrainLinf.bcSum N := by
  rw [inner_strain_e0, StrainLinf.bcSum, mul_sum, D0U0]
  apply sum_congr rfl; intro i _; rw [mul_sum]; apply sum_congr rfl; intro j _
  have hi := kk_pos i; have hj := kk_pos j; have hp := Real.pi_pos
  simp only [PiLp.zero_apply, mul_zero, Real.cos_zero, cc]
  have e1 : ((2*i+1 : ℕ) : ℝ) = kk i := by push_cast [kk]; ring
  have e2 : ((2*j+1 : ℕ) : ℝ) = kk j := by push_cast [kk]; ring
  rw [e1, e2]; field_simp; ring

/-- Hence `‖S_K(0)‖ ≥ (16/π²) bcSum N`. -/
theorem strain_norm_origin_ge (N : ℕ) :
    (16 / Real.pi ^ 2) * StrainLinf.bcSum N ≤ ‖strainAt (uK N) 0‖ := by
  rw [← strain00_origin]
  have h1 : ‖(EuclideanSpace.single (0:Fin 3) (1:ℝ) : T3)‖ = 1 := by simp
  calc _ ≤ ‖(EuclideanSpace.single (0:Fin 3) (1:ℝ) : T3)‖ * ‖strainAt (uK N) 0 (EuclideanSpace.single 0 1)‖ :=
        real_inner_le_norm _ _
    _ ≤ 1 * (‖strainAt (uK N) 0‖ * 1) := by
        rw [h1]; gcongr; simpa [h1] using (strainAt (uK N) 0).le_opNorm (EuclideanSpace.single 0 1)
    _ = _ := by ring

end PeriodicNSContinuation.StrainLinfFamily
