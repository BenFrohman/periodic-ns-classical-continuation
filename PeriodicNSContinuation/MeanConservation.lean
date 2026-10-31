/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.EnstrophyRate

/-!
# Mean conservation on `T³` (discharges `PeriodicMeanConservation ν`)

* `nlField_zero_mode` — **proved**: the nonlinear Fourier field vanishes at `k = 0`
  (the Leray projector is the identity there and `m · â(m) = 0` by incompressibility).
* `periodicMeanConservation` — **proved, unconditional**: zero-mean data stay zero-mean.
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D TorusFourierNS

namespace PeriodicNSContinuation

/-- **Proved.** For divergence-free coefficients, the nonlinear field has zero mean mode. -/
lemma nlField_zero_mode (a : FField) (hdiv : ∀ m : Mode, dot (kvec m) (a m) = 0) (i : Fin 3) :
    nlField a 0 i = 0 := by
  have hs : ∀ m : Mode, (∑ x, a m x * (((m x : ℤ)) : ℂ)) = 0 := fun m => by
    have h := hdiv m
    simp only [dot, kvec] at h
    rw [← h]; refine Finset.sum_congr rfl fun l _ => ?_
    push_cast; ring
  simp [nlField, fourierNSField, hs, lerayP, viscCoeff, kvec, ksq, dot]

/-- **Proved.** A complex function continuous on `[0,b]` with zero derivative on `(0,b)` is
constant there. -/
lemma complex_const_of_deriv_zero {f : ℝ → ℂ} {b : ℝ} (hc : ContinuousOn f (Icc 0 b))
    (hd : ∀ t ∈ Ioo 0 b, HasDerivAt f 0 t) : ∀ t ∈ Icc 0 b, f t = f 0 := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · rw [← h0]
  have hsub : Icc 0 t ⊆ Icc 0 b := Icc_subset_Icc le_rfl ht.2
  have part : ∀ L : ℂ →L[ℝ] ℝ, L (f t) = L (f 0) := fun L => by
    obtain ⟨c, hc', hceq⟩ := exists_hasDerivAt_eq_slope (fun τ => L (f τ)) (fun _ => (0:ℝ)) h0
      ((L.continuous.comp_continuousOn (hc.mono hsub)))
      (fun x hx => by
        have := L.hasFDerivAt.comp_hasDerivAt x (hd x ⟨hx.1, hx.2.trans_le ht.2⟩)
        simpa using this)
    have : L (f t) - L (f 0) = 0 := by
      have hne : (t - 0) ≠ 0 := by linarith
      field_simp at hceq; linarith
    linarith
  apply Complex.ext
  · exact part Complex.reCLM
  · exact part Complex.imCLM

/-- **Proved (unconditional).** Discharges `PeriodicMeanConservation ν`. -/
theorem periodicMeanConservation (ν : ℝ) : PeriodicMeanConservation ν := by
  intro hν u₀ u p T' hsol hmean t ht i
  have hode := periodicFourierCoeffODE ν hν u₀ u p T' hsol
  have hconst := complex_const_of_deriv_zero (fourierCoeffVF_continuousOn hsol 0 i)
    (fun τ hτ => by
      have h := hode τ hτ 0 i
      have hz : fourierNSField ν (fourierCoeffVF (u τ)) 0 i = 0 := by
        rw [fourierNSField_eq, nlField_zero_mode _
          (periodicDataDivFree (u τ) (data_of_sol hsol (Ioo_subset_Icc_self hτ)))]
        simp [viscCoeff, ksq, kvec]
      rwa [hz] at h) t ht
  rw [hconst]
  have h0 : u 0 = u₀ := funext hsol.2.2.2.2.2.2.2
  rw [h0]; exact hmean i

end PeriodicNSContinuation
