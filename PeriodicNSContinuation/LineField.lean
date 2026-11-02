/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.PlanarObstruction
import PeriodicNSContinuation.FrohmanianDirectionCoercivity

/-!
# Line-field version of Frohmanian Tether Hypothesis (B)

This version is added next to the signed version, which stays unchanged.
Coined names (November 2026): `lineGap`, `VortLineHolderHalf`, `OrthogonalStrainToLineHolder`
(`FrohmanianTetherHypothesisB_line`), `FrohmanianTetherHypothesis_line`,
`PeriodicLineDirectionCriterion`, and the lemmas below.

`lineGap a b = ‖a - ⟪a,b⟫ b‖`. For unit vectors this equals `|sin ∠(a,b)|`, so it does not see the sign.

* `lineGap_le_sub` — **proved**: for unit vectors, `|sin ∠| ≤ ‖a - b‖`.
* `vortLineHolderHalf_of_vortDirHolderHalf`, `lineB_of_signedB` — **proved**: signed (B) ⇒ line (B).
* `vortLineHolderHalf_sinShear` — **proved**: the zero-bending `sinShear` family has line gap `0`,
  so the planar obstruction does not apply to the line version.
* `periodicBKMIntegrability_of_line` — **proved (conditional)**: `PeriodicLineDirectionCriterion`
  (the classical criterion in its actual `|sin|` form, as a hypothesis, not formalized) together with
  FTH_line gives `PeriodicBKMIntegrability`. The chain from there to Statement (B) is the existing one.
-/

open Set FeffermanClayNS NavierStokes3D
open scoped RealInnerProductSpace

namespace PeriodicNSContinuation

/-- Coined. `|sin ∠(a,b)|` for unit vectors. -/
noncomputable def lineGap (a b : T3) : ℝ := ‖a - ⟪a, b⟫ • b‖

theorem lineGap_le_sub {a b : T3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) : lineGap a b ≤ ‖a - b‖ := by
  unfold lineGap
  have h1 : ‖a - ⟪a, b⟫ • b‖ ^ 2 = 1 - ⟪a, b⟫ ^ 2 := by
    rw [@norm_sub_sq_real, norm_smul, inner_smul_right, ha, hb,
      Real.norm_eq_abs, mul_one, sq_abs]; ring
  have h2 : ‖a - b‖ ^ 2 = 2 - 2 * ⟪a, b⟫ := by
    rw [@norm_sub_sq_real, ha, hb]; ring
  have : ‖a - ⟪a, b⟫ • b‖ ^ 2 ≤ ‖a - b‖ ^ 2 := by
    rw [h1, h2]; nlinarith [sq_nonneg (1 - ⟪a, b⟫)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

private lemma unit_of_ne {v : T3} (h : v ≠ 0) : ‖‖v‖⁻¹ • v‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h)]

/-- Coined. `½`-Hölder vorticity **line field** on the high set, uniform on `[0,T)`. -/
def VortLineHolderHalf (u : TimeDependentVelocity) (T : ℝ) : Prop :=
  ∃ Ω K : ℝ, 0 < Ω ∧ ∀ t ∈ Ico (0:ℝ) T, ∀ x y : T3,
    Ω ≤ ‖vorticity (u t) x‖ → Ω ≤ ‖vorticity (u t) y‖ →
      lineGap (‖vorticity (u t) x‖⁻¹ • vorticity (u t) x)
        (‖vorticity (u t) y‖⁻¹ • vorticity (u t) y) ≤ K * Real.sqrt ‖x - y‖

theorem vortLineHolderHalf_of_vortDirHolderHalf {u : TimeDependentVelocity} {T : ℝ}
    (h : VortDirHolderHalf u T) : VortLineHolderHalf u T := by
  obtain ⟨Ω, K, hΩ, hK⟩ := h
  refine ⟨Ω, K, hΩ, fun t ht x y hx hy => le_trans (lineGap_le_sub ?_ ?_) (hK t ht x y hx hy)⟩
  · exact unit_of_ne (norm_pos_iff.1 (lt_of_lt_of_le hΩ hx))
  · exact unit_of_ne (norm_pos_iff.1 (lt_of_lt_of_le hΩ hy))

/-- Coined. **OPEN.** Line version of FTH (B): bounded bending ⇒ `½`-Hölder line field. -/
def OrthogonalStrainToLineHolder (ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure), IsPeriodicMaximalSolution ν u₀ u p →
      ∀ T : ℝ, periodicTstar ν u₀ = (T : EReal) → OrthogonalStrainBounded u T →
        VortLineHolderHalf u T

/-- Coined alias. -/
abbrev FrohmanianTetherHypothesisB_line (ν : ℝ) : Prop := OrthogonalStrainToLineHolder ν

/-- Coined. **OPEN.** Line-field variant of the Frohmanian Tether Hypothesis: (A) ∧ (B_line). -/
def FrohmanianTetherHypothesis_line (ν : ℝ) : Prop :=
  FrohmanianTetherHypothesisA ν ∧ FrohmanianTetherHypothesisB_line ν

/-- **Proved.** Signed (B) ⇒ line (B). -/
theorem lineB_of_signedB {ν : ℝ} (h : FrohmanianTetherHypothesisB ν) :
    FrohmanianTetherHypothesisB_line ν :=
  fun hν u₀ hu₀ u p hm T hT hb => vortLineHolderHalf_of_vortDirHolderHalf (h hν u₀ hu₀ u p hm T hT hb)

/-- **Proved.** FTH ⇒ FTH_line. -/
theorem frohmanianTetherHypothesis_line_of_signed {ν : ℝ} (h : FrohmanianTetherHypothesis ν) :
    FrohmanianTetherHypothesis_line ν :=
  ⟨h.1, lineB_of_signedB h.2⟩

private lemma lineGap_smul_unit {e : T3} (he : ‖e‖ = 1) {c d : ℝ} (hd : d ^ 2 = 1) :
    lineGap (c • e) (d • e) = 0 := by
  unfold lineGap
  rw [inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq, he, smul_smul]
  simp only [conj_trivial, one_pow, mul_one]
  rw [show c * d * d = c * d ^ 2 by ring, hd, mul_one, sub_self, norm_zero]

/-- **Proved.** The `sinShear` family has `½`-Hölder line field with `K = 0`. -/
theorem vortLineHolderHalf_sinShear {A n : ℝ} (hn : n ≠ 0) (T : ℝ) :
    VortLineHolderHalf (fun _ => sinShear A n) T := by
  refine ⟨1, 0, one_pos, fun t _ x y hx hy => ?_⟩
  have he : ‖e3v‖ = 1 := by simp [e3v]
  have key : ∀ z : T3, vorticity (sinShear A n) z ≠ 0 →
      ∃ d : ℝ, d ^ 2 = 1 ∧ ‖vorticity (sinShear A n) z‖⁻¹ • vorticity (sinShear A n) z = d • e3v := by
    intro z hz
    rw [vorticity_sinShear hn z] at hz ⊢
    set c := A * Real.sin (n * z 0)
    have hc : c ≠ 0 := fun h => hz (by rw [h, zero_smul])
    refine ⟨|c|⁻¹ * c, ?_, ?_⟩
    · rw [mul_pow, inv_pow, sq_abs, inv_mul_cancel₀ (pow_ne_zero 2 hc)]
    · rw [norm_smul, he, mul_one, Real.norm_eq_abs, smul_smul]
  obtain ⟨d1, -, h1⟩ := key x (norm_pos_iff.1 (lt_of_lt_of_le one_pos hx))
  obtain ⟨d2, hd2, h2⟩ := key y (norm_pos_iff.1 (lt_of_lt_of_le one_pos hy))
  rw [h1, h2, lineGap_smul_unit he hd2, zero_mul]

/-- Coined. **Hypothesis (classical, in its `|sin|` form: Constantin–Fefferman 1993,
Beirão da Veiga–Berselli 2002; not formalized).** A finite lifespan rules out a `½`-Hölder line field. -/
def PeriodicLineDirectionCriterion (ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure), IsPeriodicMaximalSolution ν u₀ u p →
      ∀ T : ℝ, periodicTstar ν u₀ = (T : EReal) → ¬ VortLineHolderHalf u T

/-- **Proved (conditional).** Line criterion + FTH_line ⇒ `PeriodicBKMIntegrability`. -/
theorem periodicBKMIntegrability_of_line {ν : ℝ} (hD : PeriodicLineDirectionCriterion ν)
    (hF : FrohmanianTetherHypothesis_line ν) : PeriodicBKMIntegrability ν := by
  intro hν u₀ hu₀ u p hm T
  have htop : periodicTstar ν u₀ = ⊤ := by
    rcases tstar_eq_top_or_coe hν hu₀ with h | ⟨T', hT'⟩
    · exact h
    · exact absurd (hF.2 hν u₀ hu₀ u p hm T' hT' (hF.1 hν u₀ hu₀ u p hm T' hT'))
        (hD hν u₀ hu₀ u p hm T' hT')
  exact integrableOn_vorticity_of_lt_tstar hν hm (by rw [htop]; exact EReal.coe_lt_top T)

/-- **Proved.** The line criterion implies the signed one. -/
theorem directionCriterion_of_line {ν : ℝ} (h : PeriodicLineDirectionCriterion ν) :
    PeriodicDirectionCriterion ν :=
  fun hν u₀ hu₀ u p hm T hT hd => h hν u₀ hu₀ u p hm T hT (vortLineHolderHalf_of_vortDirHolderHalf hd)

end PeriodicNSContinuation
