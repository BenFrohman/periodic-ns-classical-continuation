/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import Mathlib

/-!
# `C¹` extension of a function on `[0, T]` by its tangent lines

If `φ` has (one-sided) derivative `φ'` within `[0, T]`, then
`tangentExt s = φ (cl s) + (s − cl s) φ' (cl s)`, with `cl s = max 0 (min s T)`, is differentiable on all
of `ℝ` with derivative `φ' (cl s)`, and agrees with `φ` on `[0, T]`.
-/

open Set Filter Topology

namespace PeriodicNSContinuation.Clamp

/-- Clamp to `[0, T]`. -/
def cl (T s : ℝ) : ℝ := max 0 (min s T)

lemma cl_of_mem {T s : ℝ} (hs : s ∈ Icc 0 T) : cl T s = s := by
  simp [cl, hs.1, hs.2]

lemma cl_mem {T : ℝ} (hT : 0 ≤ T) (s : ℝ) : cl T s ∈ Icc 0 T :=
  ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

lemma continuous_cl (T : ℝ) : Continuous (cl T) := by unfold cl; fun_prop

lemma cl_of_le {T s : ℝ} (_hT : 0 ≤ T) (hs : s ≤ 0) : cl T s = 0 := by
  simp [cl, min_le_of_left_le hs]

lemma cl_of_ge {T s : ℝ} (hT : 0 ≤ T) (hs : T ≤ s) : cl T s = T := by
  simp [cl, min_eq_right hs, hT]

/-- Tangent-line extension. -/
def tangentExt (T : ℝ) (φ φ' : ℝ → ℝ) (s : ℝ) : ℝ := φ (cl T s) + (s - cl T s) * φ' (cl T s)

theorem hasDerivAt_ext {T : ℝ} (hT : 0 < T) {φ φ' : ℝ → ℝ}
    (hd : ∀ s ∈ Icc 0 T, HasDerivWithinAt φ (φ' s) (Icc 0 T) s) (s : ℝ) :
    HasDerivAt (tangentExt T φ φ') (φ' (cl T s)) s := by
  have onI : ∀ y ∈ Icc 0 T, tangentExt T φ φ' y = φ y := fun y hy => by simp [tangentExt, cl_of_mem hy]
  have hI : ∀ y ∈ Icc 0 T, HasDerivWithinAt (tangentExt T φ φ') (φ' y) (Icc 0 T) y := fun y hy =>
    (hd y hy).congr onI (onI y hy)
  -- affine pieces
  have left : ∀ y ≤ 0, tangentExt T φ φ' y = φ 0 + y * φ' 0 := fun y hy => by
    simp [tangentExt, cl_of_le hT.le hy]
  have right : ∀ y, T ≤ y → tangentExt T φ φ' y = φ T + (y - T) * φ' T := fun y hy => by
    simp [tangentExt, cl_of_ge hT.le hy]
  have hL : ∀ y, HasDerivAt (fun y => φ 0 + y * φ' 0) (φ' 0) y := fun y => by
    simpa using ((hasDerivAt_id y).mul_const (φ' 0)).const_add (φ 0)
  have hR : ∀ y, HasDerivAt (fun y => φ T + (y - T) * φ' T) (φ' T) y := fun y => by
    simpa using (((hasDerivAt_id y).sub_const T).mul_const (φ' T)).const_add (φ T)
  rcases lt_or_ge s 0 with hs | hs
  · rw [cl_of_le hT.le hs.le]
    exact (hL s).congr_of_eventuallyEq
      (eventually_of_mem (Iio_mem_nhds hs) fun y hy => left y (le_of_lt hy))
  rcases lt_or_ge T s with hs' | hs'
  · rw [cl_of_ge hT.le hs'.le]
    exact (hR s).congr_of_eventuallyEq
      (eventually_of_mem (Ioi_mem_nhds hs') fun y hy => right y (le_of_lt hy))
  have hsI : s ∈ Icc 0 T := ⟨hs, hs'⟩
  rw [cl_of_mem hsI]
  rcases eq_or_lt_of_le hs with h0 | h0
  · subst h0
    have h1 : HasDerivWithinAt (tangentExt T φ φ') (φ' 0) (Iic 0) 0 :=
      (hL 0).hasDerivWithinAt.congr (fun y hy => left y hy) (left 0 le_rfl)
    have h2 : HasDerivWithinAt (tangentExt T φ φ') (φ' 0) (Ici 0) 0 :=
      (hI 0 hsI).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hT)
    have := h1.union h2
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  rcases eq_or_lt_of_le hs' with h1 | h1
  · rw [h1] at hsI ⊢
    have h2 : HasDerivWithinAt (tangentExt T φ φ') (φ' T) (Ici T) T :=
      (hR T).hasDerivWithinAt.congr (fun y hy => right y hy) (right T le_rfl)
    have h3 : HasDerivWithinAt (tangentExt T φ φ') (φ' T) (Iic T) T :=
      (hI T hsI).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE hT)
    have := h3.union h2
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · exact (hI s hsI).hasDerivAt (Icc_mem_nhds h0 h1)

end PeriodicNSContinuation.Clamp
