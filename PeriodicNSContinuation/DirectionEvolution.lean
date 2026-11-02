/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.BendingRateTests

/-!
# Evolution identities for the vorticity direction (attack on part (A))

Proved from the repository's `vorticity`/`curl`/`fderiv` definitions: the rotation part of `∇u`
annihilates `ω` (`fderiv_vorticity_eq_strain`), so the stretching term is `Sω`; the direction
equation `Dτ/Dt = (I−τ⊗τ)Sτ + ν|ω|⁻¹(I−τ⊗τ)L` (`hasDerivAt_vortDir_NS`); `D|ω|/Dt = α|ω| + ν τ·L`
(`hasDerivAt_norm_vorticity_lagrangian`); `|Sτ|² = |(I−τ⊗τ)Sτ|² + α²` (`norm_strain_sq_split`);
`|(I−τ⊗τ)Sτ| ≤ ‖∇u‖` (`norm_orthogonalStrain_le`).
Not derived here: the vorticity equation itself along particle paths (it is a hypothesis `hω`
of `hasDerivAt_vortDir_NS`), and no bound on `(I−τ⊗τ)Sτ` near `T*`. The only conditional
bound (`orthogonalStrainBounded_of_gradientBounded`) uses `‖∇u‖_∞ < ∞`, which is stronger than
regularity criteria (BKM) and so makes no progress on part (A).
-/

noncomputable section
open Set FeffermanClayNS NavierStokes3D
open scoped RealInnerProductSpace

namespace PeriodicNSContinuation

/-- Real scalar inner product. -/
theorem real_inner_scalar (a b : ℝ) : ⟪a, b⟫ = b * a := Real.ext_cauchy rfl

/-- Coined. Matrix entry `a i j = (A e_j)_i`. -/
def matEntry (A : T3 →L[ℝ] T3) (i j : Fin 3) : ℝ := A (EuclideanSpace.single j 1) i

/-- **Proved.** Coordinates of `A w`. -/
theorem apply_coord (A : T3 →L[ℝ] T3) (w : T3) (i : Fin 3) :
    A w i = ∑ j, matEntry A i j * w j := by
  have hw : w = ∑ j, w j • EuclideanSpace.single j (1:ℝ) := by
    ext k; fin_cases k <;> simp [Fin.sum_univ_three, Pi.single_apply]
  conv_lhs => rw [hw]
  simp [map_sum, map_smul, matEntry, mul_comm]

/-- **Proved.** Coordinates of `Aᵀ w`. -/
theorem adjoint_coord (A : T3 →L[ℝ] T3) (w : T3) (i : Fin 3) :
    ContinuousLinearMap.adjoint A w i = ∑ j, matEntry A j i * w j := by
  have : ContinuousLinearMap.adjoint A w i =
      ⟪EuclideanSpace.single i (1:ℝ), ContinuousLinearMap.adjoint A w⟫ := by
    rw [PiLp.inner_apply]; fin_cases i <;> simp [Fin.sum_univ_three, real_inner_scalar]
  rw [this, ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply]
  simp only [matEntry, Fin.sum_univ_three, real_inner_scalar]; ring

/-- **Proved.** For a differentiable field, the directional coordinate is the Jacobian entry. -/
theorem directionalCoord_eq_matEntry {v : VelocityField} {x : T3} (hd : DifferentiableAt ℝ v x)
    (i j : Fin 3) : directionalCoord v i j x = matEntry (fderiv ℝ v x) i j := by
  have h := ((EuclideanSpace.proj i : T3 →L[ℝ] ℝ).hasFDerivAt).comp x hd.hasFDerivAt
  unfold directionalCoord matEntry
  rw [show (fun y => v y i) = (EuclideanSpace.proj i : T3 →L[ℝ] ℝ) ∘ v from rfl, h.fderiv]
  rfl

/-- Coined. The curl vector read off a Jacobian matrix. -/
def curlOfMat (A : T3 →L[ℝ] T3) : T3 :=
  EuclideanSpace.single 0 (matEntry A 2 1 - matEntry A 1 2) +
    EuclideanSpace.single 1 (matEntry A 0 2 - matEntry A 2 0) +
    EuclideanSpace.single 2 (matEntry A 1 0 - matEntry A 0 1)

/-- **Proved.** `(A − Aᵀ) ω = ω × ω = 0` when `ω` is the curl of `A`. -/
theorem apply_curlOfMat_eq_adjoint (A : T3 →L[ℝ] T3) :
    A (curlOfMat A) = ContinuousLinearMap.adjoint A (curlOfMat A) := by
  ext i
  rw [apply_coord, adjoint_coord]
  fin_cases i <;>
    simp [Fin.sum_univ_three, curlOfMat, EuclideanSpace.single_apply] <;> ring

/-- **Proved.** The vorticity is the curl of the Jacobian. -/
theorem vorticity_eq_curlOfMat {v : VelocityField} {x : T3} (hd : DifferentiableAt ℝ v x) :
    vorticity v x = curlOfMat (fderiv ℝ v x) := by
  show curl v x = _
  simp only [curl, curlOfMat, directionalCoord_eq_matEntry hd]

/-- **Proved.** The vortex-stretching term: `(ω·∇)u = S ω` (the rotation part drops out). -/
theorem fderiv_vorticity_eq_strain {v : VelocityField} {x : T3} (hd : DifferentiableAt ℝ v x) :
    fderiv ℝ v x (vorticity v x) = strainAt v x (vorticity v x) := by
  rw [vorticity_eq_curlOfMat hd]
  simp only [strainAt, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ← apply_curlOfMat_eq_adjoint]
  rw [← two_smul ℝ, smul_smul]; norm_num

/-- **Proved.** Same for the direction `τ = ω/|ω|`: `(τ·∇)u = S τ`. -/
theorem fderiv_vortDir_eq_strain {v : VelocityField} {x : T3} (hd : DifferentiableAt ℝ v x) :
    fderiv ℝ v x (vortDir v x) = strainAt v x (vortDir v x) := by
  simp only [vortDir, map_smul, fderiv_vorticity_eq_strain hd]

/-- Coined. Stretching rate `α = τ · S τ`. -/
def stretchRate (v : VelocityField) (x : T3) : ℝ := ⟪vortDir v x, strainAt v x (vortDir v x)⟫

/-- **Proved.** Pythagoras: `|Sτ|² = |(I−τ⊗τ)Sτ|² + α²` where `ω ≠ 0`. -/
theorem norm_strain_sq_split {v : VelocityField} {x : T3} (h : vorticity v x ≠ 0) :
    ‖strainAt v x (vortDir v x)‖ ^ 2 = ‖orthogonalStrain v x‖ ^ 2 + stretchRate v x ^ 2 := by
  have ht : ‖vortDir v x‖ = 1 := by
    rw [vortDir, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h)]
  set t := vortDir v x
  set w := strainAt v x t
  have hsplit : w = perpPart t w + ⟪t, w⟫ • t := strain_split t w
  have horth : ⟪perpPart t w, ⟪t, w⟫ • t⟫ = 0 := by
    rw [inner_smul_right, real_inner_comm t, inner_perpPart ht, mul_zero]
  have := norm_add_sq_real (perpPart t w) (⟪t, w⟫ • t)
  rw [← hsplit, horth, norm_smul, ht, Real.norm_eq_abs] at this
  rw [orthogonalStrain, stretchRate, this]
  simp only [mul_one, sq_abs, mul_zero, add_zero]; rfl

/-- **Proved.** Hence `|(I−τ⊗τ)Sτ| ≤ |∇u|` (operator norm). -/
theorem norm_orthogonalStrain_le {v : VelocityField} {x : T3} :
    ‖orthogonalStrain v x‖ ≤ ‖fderiv ℝ v x‖ := by
  by_cases h : vorticity v x = 0
  · simp [orthogonalStrain, vortDir, h, perpPart]
  have ht : ‖vortDir v x‖ = 1 := by
    rw [vortDir, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h)]
  have h1 : ‖orthogonalStrain v x‖ ≤ ‖strainAt v x (vortDir v x)‖ := by
    have := norm_strain_sq_split h
    nlinarith [norm_nonneg (orthogonalStrain v x), norm_nonneg (strainAt v x (vortDir v x)),
      sq_nonneg (stretchRate v x)]
  have h2 : ‖strainAt v x (vortDir v x)‖ ≤ ‖strainAt v x‖ := by
    simpa [ht] using (strainAt v x).le_opNorm (vortDir v x)
  have h3 : ‖strainAt v x‖ ≤ ‖fderiv ℝ v x‖ := by
    set A := fderiv ℝ v x
    have hA : ‖ContinuousLinearMap.adjoint A‖ = ‖A‖ := LinearIsometryEquiv.norm_map _ _
    have : strainAt v x = (1/2 : ℝ) • (A + ContinuousLinearMap.adjoint A) := rfl
    rw [this, norm_smul]
    have h4 : ‖A + ContinuousLinearMap.adjoint A‖ ≤ ‖A‖ + ‖ContinuousLinearMap.adjoint A‖ :=
      norm_add_le _ _
    rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    linarith
  linarith

/-- **Proved.** Lagrangian evolution of `|ω|`: if `Dω/Dt = S ω + ν L`, `ω ≠ 0`, then
`D|ω|/Dt = α |ω| + ν τ·L` with `τ = ω/|ω|`, `α = τ·Sτ`. -/
theorem hasDerivAt_norm_vorticity_lagrangian {ω : ℝ → T3} {S : T3 →L[ℝ] T3} {L : T3} {ν s : ℝ}
    (hω : HasDerivAt ω (S (ω s) + ν • L) s) (h0 : ω s ≠ 0) :
    HasDerivAt (fun r => ‖ω r‖)
      (⟪‖ω s‖⁻¹ • ω s, S (‖ω s‖⁻¹ • ω s)⟫ * ‖ω s‖ + ν * ⟪‖ω s‖⁻¹ • ω s, L⟫) s := by
  have hn : 0 < ‖ω s‖ := norm_pos_iff.2 h0
  have hsq := hω.norm_sq
  have hsq0 : ‖ω s‖ ^ 2 ≠ 0 := by positivity
  have := hsq.sqrt hsq0
  simp only [Real.sqrt_sq (norm_nonneg _)] at this
  convert this using 1
  simp only [map_smul, inner_smul_left, inner_smul_right, inner_add_right, RCLike.conj_to_real]
  field_simp

/-- **Proved.** Direction equation with the true stretching term: if along a trajectory the
vorticity obeys `Dω/Dt = (ω·∇)u + ν L` and at time `s` equals `ω(x)` for the field `v`
(differentiable at `x`, `ω ≠ 0`), then `Dτ/Dt = (I−τ⊗τ)Sτ + ν|ω|⁻¹(I−τ⊗τ)L`. -/
theorem hasDerivAt_vortDir_NS {v : VelocityField} {x : T3} {ω : ℝ → T3} {L : T3} {ν s : ℝ}
    (hd : DifferentiableAt ℝ v x) (hs : ω s = vorticity v x)
    (hω : HasDerivAt ω (fderiv ℝ v x (ω s) + ν • L) s) (h0 : ω s ≠ 0) :
    HasDerivAt (fun r => ‖ω r‖⁻¹ • ω r)
      (orthogonalStrain v x + (ν * ‖ω s‖⁻¹) • perpPart (vortDir v x) L) s := by
  have hω' : HasDerivAt ω (strainAt v x (ω s) + ν • L) s := by
    rw [hs, ← fderiv_vorticity_eq_strain hd, ← hs]; exact hω
  have := hasDerivAt_vortDir_lagrangian hω' h0
  rw [hs] at this ⊢
  exact this

/-- Coined. Known-type quantity: `‖∇u‖_∞` bounded on `[0,T)`. -/
def GradientBoundedUpTo (u : TimeDependentVelocity) (T : ℝ) : Prop :=
  ∃ M, ∀ t ∈ Ico 0 T, ∀ x, ‖fderiv ℝ (u t) x‖ ≤ M

/-- **Proved (conditional).** Bounded velocity gradient gives part (A)'s bound for one solution.
The hypothesis is strictly stronger than the conclusion and, by BKM, already excludes blow-up. -/
theorem orthogonalStrainBounded_of_gradientBounded {u : TimeDependentVelocity} {T : ℝ}
    (h : GradientBoundedUpTo u T) : OrthogonalStrainBounded u T := by
  obtain ⟨M, hM⟩ := h
  exact ⟨1, M, one_pos, fun t ht x _ => norm_orthogonalStrain_le.trans (hM t ht x)⟩

end PeriodicNSContinuation
