/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.Corrected
import Mathlib.Analysis.ODE.Gronwall

/-!
# (1) Uniqueness: Grönwall closes the energy argument

Classical argument: for two smooth periodic solutions `u, v` from the same data, the difference
energy `E(t) = ∫_{[0,1]³} |u − v|²` satisfies `E(0) = 0` and `E' ≤ 2‖∇v‖_{L∞([0,T]×𝕋³)} E`.
Grönwall then forces `E ≡ 0`.

Proved here: the Grönwall step (`eq_zero_of_deriv_le_mul`) and the reduction
`periodicVelocityUniqueness_of_energy`. Named, not proved: the energy inequality itself,
`PeriodicEnergyDifferenceEstimate`.
-/

open FeffermanClayNS NavierStokes3D Set Filter Topology

namespace PeriodicNSContinuation.Corrected

/-- **Proved (Grönwall):** a continuous `E` on `[0, T]` with right derivative `E' ≤ L E` and
`E 0 ≤ 0` satisfies `E ≤ 0` on `[0, T]`. -/
theorem eq_zero_of_deriv_le_mul {E E' : ℝ → ℝ} {L T : ℝ}
    (hc : ContinuousOn E (Icc 0 T))
    (hd : ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt E (E' t) (Ici t) t)
    (hb : ∀ t ∈ Ico (0 : ℝ) T, E' t ≤ L * E t) (h0 : E 0 ≤ 0) :
    ∀ t ∈ Icc (0 : ℝ) T, E t ≤ 0 := by
  intro t ht
  have := le_gronwallBound_of_liminf_deriv_right_le (ε := 0) (K := L) hc
    (fun x hx _r hr => (hd x hx).liminf_right_slope_le hr) h0
    (fun x hx => by simpa using hb x hx) t ht
  simpa [gronwallBound_ε0_δ0] using this

/-- **Classical (not formalized): the energy inequality for the difference of two solutions.**
For two corrected periodic smooth solutions on `[0, T]` from the same data there is a function
`E` (classically `∫_{[0,1]³} |u − v|²`) that is continuous on `[0, T]`, has right derivative
`E' ≤ L E` on `[0, T)`, satisfies `E 0 ≤ 0`, and whose vanishing forces `u t = v t`. -/
def PeriodicEnergyDifferenceEstimate (ν : ℝ) : Prop :=
  ∀ (u₀ : VelocityField) (T : ℝ) (u v : TimeDependentVelocity) (p q : TimeDependentPressure),
    IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p →
    IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T v q →
    ∃ (E E' : ℝ → ℝ) (L : ℝ), ContinuousOn E (Icc 0 T) ∧
      (∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt E (E' t) (Ici t) t) ∧
      (∀ t ∈ Ico (0 : ℝ) T, E' t ≤ L * E t) ∧ E 0 ≤ 0 ∧
      (∀ t ∈ Icc (0 : ℝ) T, E t ≤ 0 → u t = v t)

/-- **Proved:** the energy inequality implies velocity uniqueness. -/
theorem periodicVelocityUniqueness_of_energy (ν : ℝ) (h : PeriodicEnergyDifferenceEstimate ν) :
    PeriodicVelocityUniqueness ν := by
  intro u₀ T u v p q hu hv t ht
  obtain ⟨E, E', L, hc, hd, hb, h0, hz⟩ := h u₀ T u v p q hu hv
  exact hz t ht (eq_zero_of_deriv_le_mul hc hd hb h0 t ht)

end PeriodicNSContinuation.Corrected
