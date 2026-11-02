/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.BiotSavartCoeff

/-!
# Fourier Biot–Savart law for velocity and strain, and aligned-mode vanishing

For smooth periodic divergence-free data and `k ≠ 0` (unit-cell coefficients):
`û_k = i (k×ω̂_k)/(2π|k|²)` (`fourierCoeffVF_eq_biotSavart`) and
`Ŝ_k = −(k⊗(k×ω̂_k) + (k×ω̂_k)⊗k)/(2|k|²)` (`strainCoeff_eq_symbol`).
A mode with `ω̂_k ∥ τ` contributes zero to `Ŝ_k τ` (`strainCoeff_apply_aligned`), since
`k·ω̂_k = 0` forces `k·τ = 0`. Misaligned modes do contribute to the bending
(`symApply_misaligned_example`). Nothing here bounds the bending vector near `T*`.
-/

noncomputable section
open Set MeasureTheory FeffermanClayNS NavierStokes3D TorusFourierNS

namespace PeriodicNSContinuation

lemma ksq_ne_zero_of_ne {k : Mode} (hk : k ≠ 0) : (ksq (kvec k) : ℂ) ≠ 0 := by
  norm_cast
  intro h0; apply hk; funext l
  have : ∀ m ∈ (Finset.univ : Finset (Fin 3)), kvec k m ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun m _ => sq_nonneg _).1 h0
  have := this l (Finset.mem_univ _)
  simpa [kvec] using this

/-- **Proved.** Biot–Savart for the velocity: `û_k = i (k × ω̂_k) / (2π |k|²)`, `k ≠ 0`. -/
theorem fourierCoeffVF_eq_biotSavart {v : VelocityField} (hv : IsPeriodicSmoothInitialData v)
    {k : Mode} (hk : k ≠ 0) (i : Fin 3) :
    fourierCoeffVF v k i = Complex.I * crossC (kvec k) (vortCoeff v k) i /
      (2 * Real.pi * (ksq (kvec k) : ℂ)) := by
  have hdiv := periodicDataDivFree v hv k
  have hks := ksq_ne_zero_of_ne hk
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hv' : ∀ a, vortCoeff v k a = _ := vortCoeff_eq hv k
  simp only [dot, Fin.sum_univ_three] at hdiv
  simp only [ksq, Fin.sum_univ_three] at hks ⊢
  rw [eq_div_iff (mul_ne_zero (mul_ne_zero two_ne_zero hpi) hks)]
  simp only [crossC, hv', kvec]
  fin_cases i <;> simp [kvec] at hdiv ⊢
  all_goals
    first
    | (linear_combination (norm := skip) (2 * Real.pi * (k 0 : ℂ)) * hdiv
       ring_nf; simp only [Complex.I_sq]; ring1)
    | (linear_combination (norm := skip) (2 * Real.pi * (k 1 : ℂ)) * hdiv
       ring_nf; simp only [Complex.I_sq]; ring1)
    | (linear_combination (norm := skip) (2 * Real.pi * (k 2 : ℂ)) * hdiv
       ring_nf; simp only [Complex.I_sq]; ring1)

/-- Coined. Unit-cell Fourier coefficient of the strain `S_ij = ½(∂_j u_i + ∂_i u_j)`. -/
def strainCoeff (v : VelocityField) (k : Mode) (i j : Fin 3) : ℂ :=
  (gradCoeff v k i j + gradCoeff v k j i) / 2

/-- Coined. Biot–Savart strain symbol acting on a vorticity coefficient `w`:
`Ŝ_ij = −(k_j (k×w)_i + k_i (k×w)_j) / (2|k|²)`. -/
def strainSymW (k : Fin 3 → ℝ) (w : Fin 3 → ℂ) (i j : Fin 3) : ℂ :=
  -((k j : ℂ) * crossC k w i + (k i : ℂ) * crossC k w j) / (2 * (ksq k : ℂ))

/-- **Proved.** Fourier Biot–Savart for the strain: `Ŝ_k = strainSymW k ω̂_k`, `k ≠ 0`. -/
theorem strainCoeff_eq_symbol {v : VelocityField} (hv : IsPeriodicSmoothInitialData v)
    {k : Mode} (hk : k ≠ 0) (i j : Fin 3) :
    strainCoeff v k i j = strainSymW (kvec k) (vortCoeff v k) i j := by
  have hks := ksq_ne_zero_of_ne hk
  rw [strainCoeff, strainSymW, gradCoeff_eq_vort hv hk, gradCoeff_eq_vort hv hk]
  simp only [kvec]
  field_simp
  ring

/-- **Proved.** The vorticity coefficients are divergence-free: `k · ω̂_k = 0`. -/
theorem vortCoeff_div {v : VelocityField} (hv : IsPeriodicSmoothInitialData v) (k : Mode) :
    ∑ j, (kvec k j : ℂ) * vortCoeff v k j = 0 := by
  simp only [vortCoeff_eq hv k, Fin.sum_univ_three, crossC]
  simp
  ring

/-- Coined. The symbol applied to a real direction `τ`: `(Ŝ τ)_i`. -/
def symApply (k : Fin 3 → ℝ) (w : Fin 3 → ℂ) (τ : Fin 3 → ℝ) (i : Fin 3) : ℂ :=
  ∑ j, strainSymW k w i j * (τ j : ℂ)

/-- **Proved.** `(Ŝτ)_i = −((k·τ)(k×w)_i + k_i (k×w)·τ) / (2|k|²)`. -/
theorem symApply_eq (k : Fin 3 → ℝ) (w : Fin 3 → ℂ) (τ : Fin 3 → ℝ) (i : Fin 3) :
    symApply k w τ i = -((∑ j, (k j : ℂ) * (τ j : ℂ)) * crossC k w i +
      (k i : ℂ) * ∑ j, crossC k w j * (τ j : ℂ)) / (2 * (ksq k : ℂ)) := by
  simp only [symApply, strainSymW, Fin.sum_univ_three]
  ring

/-- **Proved.** Aligned-mode vanishing: if a divergence-free mode `w` is parallel to `τ`
(`w = c τ`, `k·w = 0`), it contributes nothing to `Sτ` (neither stretching nor bending). -/
theorem symApply_aligned (k : Fin 3 → ℝ) (τ : Fin 3 → ℝ) (c : ℂ)
    (hdiv : ∑ j, (k j : ℂ) * (c * (τ j : ℂ)) = 0) (i : Fin 3) :
    symApply k (fun j => c * (τ j : ℂ)) τ i = 0 := by
  rw [symApply_eq, div_eq_zero_iff]
  left
  simp only [Fin.sum_univ_three] at hdiv
  simp only [Fin.sum_univ_three, crossC]
  fin_cases i <;> simp
  · linear_combination (-((k 1 : ℂ) * (τ 2 : ℂ) - (k 2 : ℂ) * (τ 1 : ℂ))) * hdiv
  · linear_combination (-((k 2 : ℂ) * (τ 0 : ℂ) - (k 0 : ℂ) * (τ 2 : ℂ))) * hdiv
  · linear_combination (-((k 0 : ℂ) * (τ 1 : ℂ) - (k 1 : ℂ) * (τ 0 : ℂ))) * hdiv

/-- **Proved.** Stretching part alone vanishes for parallel `w` without any divergence condition:
`τ · Ŝ(cτ) τ = 0`. -/
theorem stretch_symApply_parallel (k τ : Fin 3 → ℝ) (c : ℂ) :
    ∑ i, (τ i : ℂ) * symApply k (fun j => c * (τ j : ℂ)) τ i = 0 := by
  simp only [symApply_eq, Fin.sum_univ_three, crossC]
  simp
  ring

/-- **Proved.** For the repository's smooth periodic data: a Fourier mode whose vorticity
coefficient is parallel to `τ` contributes zero to `Ŝ_k τ`. -/
theorem strainCoeff_apply_aligned {v : VelocityField} (hv : IsPeriodicSmoothInitialData v)
    {k : Mode} (hk : k ≠ 0) (τ : Fin 3 → ℝ) (c : ℂ)
    (hal : ∀ j, vortCoeff v k j = c * (τ j : ℂ)) (i : Fin 3) :
    ∑ j, strainCoeff v k i j * (τ j : ℂ) = 0 := by
  have hw : vortCoeff v k = fun j => c * (τ j : ℂ) := funext hal
  have hdiv := vortCoeff_div hv k
  rw [hw] at hdiv
  simp only [strainCoeff_eq_symbol hv hk, hw]
  exact symApply_aligned _ τ c hdiv i

/-- **Proved.** Misaligned modes do bend: `k = e₁`, `w = e₃`, `τ = e₂` gives `(Ŝτ)₁ = ½ ≠ 0`,
a component orthogonal to `τ`. So the vanishing above is genuinely limited to aligned modes. -/
theorem symApply_misaligned_example :
    symApply ![1, 0, 0] ![0, 0, 1] ![0, 1, 0] 0 = 1 / 2 := by
  rw [symApply_eq]
  simp [Fin.sum_univ_three, crossC, ksq]

end PeriodicNSContinuation
