/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.CommutatorAssembly

/-!
# Toward `PeriodicLowFreqVorticityBound`: Fourier multipliers as kernels on the unit cell

A finitely supported Fourier multiplier `m` acts on a continuous function `g` by convolution with
the trigonometric polynomial `K(z) = Σ_k m(k) e(k·z)`. Hence the multiplier is bounded on `L^∞`
by the (translated) unit-cell `L¹` norm of `K` (Young's inequality, `L¹ * L^∞`).
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D TorusFourierNS

namespace PeriodicNSContinuation

/-- Coined. The character `e(k·x) = exp(2πi k·x)` on `ℝ³`. -/
def charE (k : Mode) (x : Fin 3 → ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ∑ j, ((k j : ℝ) : ℂ) * (x j : ℂ))

/-- Coined. Kernel of a multiplier supported on the finite set `S`. -/
def multKernel (S : Finset Mode) (m : Mode → ℂ) (z : Fin 3 → ℝ) : ℂ :=
  ∑ k ∈ S, m k * charE k z

lemma continuous_charE (k : Mode) : Continuous (charE k) := by
  unfold charE; fun_prop

lemma continuous_multKernel (S : Finset Mode) (m : Mode → ℂ) : Continuous (multKernel S m) :=
  continuous_finset_sum _ fun k _ => continuous_const.mul (continuous_charE k)

lemma charE_sub (k : Mode) (x y : Fin 3 → ℝ) :
    charE k (x - y) = charE k x *
      Complex.exp (-(2 * Real.pi * Complex.I) * ∑ j, ((k j : ℝ) : ℂ) * (y j : ℂ)) := by
  unfold charE
  rw [← Complex.exp_add]; congr 1
  simp only [Pi.sub_apply, Complex.ofReal_sub, mul_sub, Finset.sum_sub_distrib]; ring

/-- **Proved.** A finitely supported multiplier applied to the Fourier coefficients of `g` is
the convolution of `g` with `multKernel`. -/
theorem multiplier_eq_conv {g : (Fin 3 → ℝ) → ℂ} (hg : Continuous g) (S : Finset Mode)
    (m : Mode → ℂ) (x : Fin 3 → ℝ) :
    ∑ k ∈ S, m k * cubeCoeff g k * charE k x =
      ∫ y in Icc (0 : Fin 3 → ℝ) 1, g y * multKernel S m (x - y) := by
  have hi : ∀ k, IntegrableOn (fun y => g y * (m k * charE k (x - y))) (Icc (0 : Fin 3 → ℝ) 1) :=
    fun k => (hg.mul (continuous_const.mul
      ((continuous_charE k).comp (continuous_const.sub continuous_id)))).continuousOn
        |>.integrableOn_compact isCompact_Icc
  simp only [multKernel, Finset.mul_sum]
  rw [integral_finset_sum _ fun k _ => hi k]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [cubeCoeff, charE_sub]
  rw [mul_comm (m k), mul_assoc]
  refine (integral_mul_const (m k * charE k x) _).symm.trans ?_
  congr 1; funext y; ring

/-- **Proved.** `L¹ * L^∞` bound: if `‖g‖ ≤ B` on the cell, the multiplier output at `x` is at
most `B · ∫_{[0,1]³} ‖K(x - y)‖ dy`. -/
theorem norm_multiplier_le {g : (Fin 3 → ℝ) → ℂ} (hg : Continuous g) {B : ℝ}
    (hB : ∀ y ∈ Icc (0 : Fin 3 → ℝ) 1, ‖g y‖ ≤ B) (S : Finset Mode) (m : Mode → ℂ)
    (x : Fin 3 → ℝ) :
    ‖∑ k ∈ S, m k * cubeCoeff g k * charE k x‖ ≤
      B * ∫ y in Icc (0 : Fin 3 → ℝ) 1, ‖multKernel S m (x - y)‖ := by
  have hK : Continuous fun y => multKernel S m (x - y) :=
    (continuous_multKernel S m).comp (continuous_const.sub continuous_id)
  rw [multiplier_eq_conv hg S m x, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine setIntegral_mono_on ((hg.mul hK).norm.continuousOn.integrableOn_compact isCompact_Icc)
    ((continuous_const.mul hK.norm).continuousOn.integrableOn_compact isCompact_Icc)
    measurableSet_Icc fun y hy => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hB y hy) (norm_nonneg _)

end PeriodicNSContinuation
