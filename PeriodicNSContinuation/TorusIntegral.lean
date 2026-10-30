/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import WeightedEnstrophy.TorusCalculus

/-!
# Order facts for `WeightedEnstrophy.Torus.torusIntegral`

Monotonicity on the unit cube, and: a continuous function that is nonnegative on the cube and has
nonpositive integral vanishes on the cube.
-/

open MeasureTheory Set WeightedEnstrophy.Torus

namespace PeriodicNSContinuation.Torus

lemma integral01_mono {φ ψ : ℝ → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : ∀ x ∈ Icc (0 : ℝ) 1, φ x ≤ ψ x) : ∫ x in (0:ℝ)..1, φ x ≤ ∫ x in (0:ℝ)..1, ψ x :=
  intervalIntegral.integral_mono_on zero_le_one (hφ.intervalIntegrable 0 1)
    (hψ.intervalIntegrable 0 1) h

lemma integral01_eq_zero {φ : ℝ → ℝ} (hφ : Continuous φ) (h0 : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ φ x)
    (hle : ∫ x in (0:ℝ)..1, φ x ≤ 0) : ∀ x ∈ Icc (0 : ℝ) 1, φ x = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨c, hc, hcne⟩ := hne
  have hlt := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := fun _ => (0 : ℝ)) (g := φ) zero_lt_one continuousOn_const hφ.continuousOn
    (fun x hx => h0 x (Ioc_subset_Icc_self hx)) ⟨c, hc, lt_of_le_of_ne (h0 c hc) (Ne.symm hcne)⟩
  simp at hlt
  linarith

theorem torusIntegral_mono_on {f g : E → ℝ} (hf : Continuous f) (hg : Continuous g) (t : ℝ)
    (h : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, ∀ c ∈ Icc (0 : ℝ) 1,
      f (t, a, b, c) ≤ g (t, a, b, c)) :
    torusIntegral f t ≤ torusIntegral g t := by
  have c3f := cont_i3 hf; have c3g := cont_i3 hg
  have c2f := cont_i2 hf; have c2g := cont_i2 hg
  refine integral01_mono (by fun_prop) (by fun_prop) fun a ha => ?_
  refine integral01_mono (by fun_prop) (by fun_prop) fun b hb => ?_
  exact integral01_mono (by fun_prop) (by fun_prop) fun c hc => h a ha b hb c hc

theorem eq_zero_of_torusIntegral_nonpos {f : E → ℝ} (hf : Continuous f) (t : ℝ)
    (h0 : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, ∀ c ∈ Icc (0 : ℝ) 1, 0 ≤ f (t, a, b, c))
    (hle : torusIntegral f t ≤ 0) :
    ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, ∀ c ∈ Icc (0 : ℝ) 1, f (t, a, b, c) = 0 := by
  have c3f := cont_i3 hf
  have c2f := cont_i2 hf
  have n3 : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, 0 ≤ i3 f (t, a, b) := fun a ha b hb => by
    have := integral01_mono (φ := fun _ => (0 : ℝ)) continuous_const (by fun_prop)
      (fun c hc => h0 a ha b hb c hc)
    simpa [i3] using this
  have n2 : ∀ a ∈ Icc (0 : ℝ) 1, 0 ≤ i2 f (t, a) := fun a ha => by
    have := integral01_mono (φ := fun _ => (0 : ℝ)) continuous_const (by fun_prop)
      (fun b hb => n3 a ha b hb)
    simpa [i2] using this
  have z2 := integral01_eq_zero (φ := fun a => i2 f (t, a)) (by fun_prop) n2 hle
  intro a ha b hb c hc
  have z3 := integral01_eq_zero (φ := fun b => i3 f (t, a, b)) (by fun_prop) (n3 a ha)
    (le_of_eq (z2 a ha)) b hb
  exact integral01_eq_zero (φ := fun c => f (t, a, b, c)) (by fun_prop) (h0 a ha b hb)
    (le_of_eq z3) c hc

end PeriodicNSContinuation.Torus
