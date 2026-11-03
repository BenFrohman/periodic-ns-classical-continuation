/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.BendingRate

/-!
# The cubic source for the vorticity maximum, and the recorded quartic-sink gap

Companion to `paper/cubic_source/cubic_source_gap.tex`. Coined names (Nov 2026):
`quadratic_comparison`, `lifespan_lower_bound`, `cubic_comparison`, `fence_ceiling`,
`sink_ceiling`, `integral_le_of_ceiling`, `pairing_le_of_strain_bound`,
`PeriodicStrainLinfBound`, `PeriodicQuarticVorticitySink`, `bkm_bound_of_quarticSink`.

* **Proved (abstract real analysis).** `M' ≤ C M²` gives `1/M(t) ≥ 1/M₀ − C t`, so `M` stays finite
  for `t < 1/(C M₀)`; this is only a lifespan lower bound. The log-corrected rate
  `M' ≤ C M² (1 + log M)` is weakened to `M' ≤ C M³`, which gives `1/M(t)² ≥ 1/M₀² − 2 C t`: again only a
  lifespan lower bound. `M' ≤ M² (C − κ M)` with `κ > 0` gives `M ≤ max(M₀, C/κ)` for all time.
* **Conditional.** `PeriodicStrainLinfBound` (OPEN, likely false as a uniform statement: Riesz
  transforms are unbounded on `L^∞`) gives the pointwise pairing bound `ω·Sω ≤ C M³`.
* **Open.** `PeriodicQuarticVorticitySink` is never assumed. `bkm_bound_of_quarticSink` proves that
  it would bound `M` and the BKM integral `∫₀ᵀ M` uniformly for `T` below the lifespan.
-/

open Set Filter Topology MeasureTheory InnerProductSpace FeffermanClayNS NavierStokes3D
open scoped RealInnerProductSpace

namespace PeriodicNSContinuation

open Corrected

/-- **Proved.** Quadratic comparison: if `M > 0` and `M' ≤ C M²`, then `1/M 0 − C t ≤ 1/M t`. -/
theorem quadratic_comparison {M : ℝ → ℝ} {C : ℝ} (hd : Differentiable ℝ M) (hpos : ∀ t, 0 < M t)
    (hrate : ∀ t, deriv M t ≤ C * M t ^ 2) {t : ℝ} (ht : 0 ≤ t) :
    1 / M 0 - C * t ≤ 1 / M t := by
  set h : ℝ → ℝ := fun s => 1 / M s + C * s with hh
  have hder : ∀ s, HasDerivAt h (-(deriv M s) / M s ^ 2 + C) s := by
    intro s
    have h1 : HasDerivAt (fun s => 1 / M s) (-(deriv M s) / M s ^ 2) s := by
      have := ((hd s).hasDerivAt).inv (hpos s).ne'
      simpa [one_div] using this
    have := h1.add ((hasDerivAt_id' s).const_mul C); rw [mul_one] at this; exact this
  have hmono : Monotone h := by
    apply monotone_of_deriv_nonneg (fun s => (hder s).differentiableAt)
    intro s
    rw [(hder s).deriv]
    have hp := pow_pos (hpos s) 2
    have : deriv M s / M s ^ 2 ≤ C := by rw [div_le_iff₀ hp]; exact hrate s
    rw [neg_div]; linarith
  have := hmono ht
  simp only [hh, mul_zero, add_zero] at this
  linarith

/-- **Proved.** Lifespan lower bound: under `M' ≤ C M²`, for `0 ≤ t` with `C M₀ t < 1`,
`M t ≤ M₀ / (1 − C M₀ t)`. This is all the cubic source gives; it does not bound `M` for all time. -/
theorem lifespan_lower_bound {M : ℝ → ℝ} {C : ℝ} (hd : Differentiable ℝ M) (hpos : ∀ t, 0 < M t)
    (hrate : ∀ t, deriv M t ≤ C * M t ^ 2) {t : ℝ} (ht : 0 ≤ t) (hlt : C * M 0 * t < 1) :
    M t ≤ M 0 / (1 - C * M 0 * t) := by
  have h := quadratic_comparison hd hpos hrate ht
  have h0 := hpos 0; have h1 := hpos t
  have hden : 0 < 1 - C * M 0 * t := by linarith
  rw [le_div_iff₀ hden]
  have : (1 / M 0 - C * t) * (M 0 * M t) ≤ (1 / M t) * (M 0 * M t) :=
    mul_le_mul_of_nonneg_right h (by positivity)
  field_simp at this
  nlinarith [this]

/-- **Proved.** Log-corrected comparison. With `C ≥ 0`, `M' ≤ C M² (1 + log M)` implies (via
`log M ≤ M − 1`) `M' ≤ C M³`, hence `1/M 0² − 2 C t ≤ 1/M t²`. Still only a lifespan lower bound. -/
theorem cubic_comparison {M : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C) (hd : Differentiable ℝ M)
    (hpos : ∀ t, 0 < M t) (hrate : ∀ t, deriv M t ≤ C * M t ^ 2 * (1 + Real.log (M t)))
    {t : ℝ} (ht : 0 ≤ t) : 1 / M 0 ^ 2 - 2 * C * t ≤ 1 / M t ^ 2 := by
  have hcub : ∀ s, deriv M s ≤ C * M s ^ 3 := by
    intro s
    have hl := Real.log_le_sub_one_of_pos (hpos s)
    have : C * M s ^ 2 * (1 + Real.log (M s)) ≤ C * M s ^ 2 * M s :=
      mul_le_mul_of_nonneg_left (by linarith) (by have := hpos s; positivity)
    nlinarith [hrate s]
  set h : ℝ → ℝ := fun s => 1 / M s ^ 2 + 2 * C * s with hh
  have hder : ∀ s, HasDerivAt h (-(2 * M s * deriv M s) / (M s ^ 2) ^ 2 + 2 * C) s := by
    intro s
    have hsq : HasDerivAt (fun s => M s ^ 2) (2 * M s * deriv M s) s := by
      simpa [mul_comm] using ((hd s).hasDerivAt).pow 2
    have h1 := hsq.inv (pow_pos (hpos s) 2).ne'
    have h1' : HasDerivAt (fun s => 1 / M s ^ 2) (-(2 * M s * deriv M s) / (M s ^ 2) ^ 2) s := by
      simpa [one_div] using h1
    have := h1'.add ((hasDerivAt_id' s).const_mul (2 * C)); rw [mul_one] at this; exact this
  have hmono : Monotone h := by
    apply monotone_of_deriv_nonneg (fun s => (hder s).differentiableAt)
    intro s
    rw [(hder s).deriv]
    have hp := hpos s
    have hp4 : 0 < (M s ^ 2) ^ 2 := by positivity
    have : 2 * M s * deriv M s / (M s ^ 2) ^ 2 ≤ 2 * C := by
      rw [div_le_iff₀ hp4]; nlinarith [hcub s, pow_pos hp 3]
    rw [neg_div]; linarith
  have := hmono ht
  simp only [hh, mul_zero, add_zero] at this
  linarith

/-- **Proved.** Fencing with a ceiling. On `[a,b]`, if `M` is continuous, has right derivative
`M' x ≤ M x² (C − κ M x)` with `κ > 0`, and `c ≥ max (M a) (C/κ)`, `c ≥ 0`, then `M ≤ c` on `[a,b]`. -/
theorem fence_ceiling {M M' : ℝ → ℝ} {a b C κ c : ℝ} (hκ : 0 < κ) (hc0 : 0 ≤ c)
    (hcC : C / κ ≤ c) (hca : M a ≤ c) (hcont : ContinuousOn M (Icc a b))
    (hder : ∀ x ∈ Ico a b, HasDerivWithinAt M (M' x) (Ici x) x)
    (hrate : ∀ x ∈ Ico a b, M' x ≤ M x ^ 2 * (C - κ * M x)) :
    ∀ x ∈ Icc a b, M x ≤ c := by
  intro x hx
  have hCk : C ≤ κ * c := by rwa [div_le_iff₀ hκ, mul_comm] at hcC
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have := image_le_of_deriv_right_lt_deriv_boundary (f := M) (f' := M') (B := fun _ => c + ε)
    (B' := fun _ => 0) hcont hder (by linarith) (fun _ => hasDerivAt_const _ _) ?_ hx
  · exact this
  intro y hy hEq
  have hpos : 0 < M y := by linarith
  have hneg : C - κ * M y < 0 := by nlinarith
  have : M y ^ 2 * (C - κ * M y) < 0 := mul_neg_of_pos_of_neg (by positivity) hneg
  linarith [hrate y hy]

/-- **Proved.** Sink ceiling: if `M' ≤ M²(C − κ M)` everywhere with `κ > 0`, `M` differentiable,
`0 ≤ M 0 ≤ C/κ`, then `M t ≤ C/κ` for all `t ≥ 0`. -/
theorem sink_ceiling {M : ℝ → ℝ} {C κ : ℝ} (hκ : 0 < κ) (hd : Differentiable ℝ M)
    (hrate : ∀ t, deriv M t ≤ M t ^ 2 * (C - κ * M t)) (h00 : 0 ≤ M 0) (h0 : M 0 ≤ C / κ)
    {t : ℝ} (ht : 0 ≤ t) : M t ≤ C / κ :=
  fence_ceiling (M' := deriv M) (a := 0) (b := t) hκ (le_trans h00 h0) le_rfl h0
    hd.continuous.continuousOn (fun x _ => (hd x).hasDerivAt.hasDerivWithinAt)
    (fun x _ => hrate x) t ⟨ht, le_rfl⟩

/-- **Proved.** A ceiling `M ≤ c` on `[0,T]` with `M` continuous gives a finite BKM integral
`∫₀ᵀ M ≤ c T`. -/
theorem integral_le_of_ceiling {M : ℝ → ℝ} {T c : ℝ} (hT : 0 ≤ T)
    (hcont : ContinuousOn M (Icc 0 T)) (hc : ∀ x ∈ Icc 0 T, M x ≤ c) :
    IntegrableOn M (Icc 0 T) ∧ ∫ x in (0:ℝ)..T, M x ≤ c * T := by
  refine ⟨hcont.integrableOn_Icc, ?_⟩
  have := intervalIntegral.integral_mono_on hT (hcont.intervalIntegrable_of_Icc hT)
    (intervalIntegrable_const (μ := volume) (c := c)) hc
  simpa [mul_comm] using this

/-- **Proved.** Pairing from a strain bound: `‖w‖ ≤ M`, `‖S‖ ≤ C M` give `⟪w, S w⟫ ≤ C M³`. -/
theorem pairing_le_of_strain_bound {S : T3 →L[ℝ] T3} {w : T3} {M C : ℝ}
    (hw : ‖w‖ ≤ M) (hS : ‖S‖ ≤ C * M) : inner ℝ w (S w) ≤ C * M ^ 3 := by
  have h1 : inner ℝ w (S w) ≤ ‖w‖ * ‖S w‖ := real_inner_le_norm _ _
  have h2 : ‖S w‖ ≤ ‖S‖ * ‖w‖ := S.le_opNorm w
  have hM : 0 ≤ M := le_trans (norm_nonneg _) hw
  have hn := norm_nonneg w
  calc inner ℝ w (S w) ≤ ‖w‖ * (‖S‖ * ‖w‖) := h1.trans (mul_le_mul_of_nonneg_left h2 hn)
    _ ≤ M * (C * M * M) := by
        apply mul_le_mul hw _ (by positivity) hM
        exact mul_le_mul hS hw hn (le_trans (norm_nonneg _) hS)
    _ = C * M ^ 3 := by ring

/-- Coined (Nov 2026). **OPEN, and likely false as stated.** A uniform pointwise `L^∞` strain bound
`‖S(t,x)‖ ≤ C ‖ω(t)‖_∞` along smooth maximal solutions. Calderón–Zygmund theory does not give it
(Riesz transforms are unbounded on `L^∞`); the classical bound carries a factor
`1 + log⁺(‖ω‖_{H^s}/‖ω‖_∞)`. Never assumed anywhere. -/
def PeriodicStrainLinfBound (ν : ℝ) : Prop :=
  0 < ν → ∃ C : ℝ, 0 ≤ C ∧ ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure), IsPeriodicMaximalSolution ν u₀ u p →
      ∀ t : ℝ, 0 ≤ t → (t : EReal) < periodicTstar ν u₀ → ∀ x : T3,
        ‖strainAt (u t) x‖ ≤ C * vorticity_sup_norm (vorticity (u t))

/-- **Proved (conditional).** Under `PeriodicStrainLinfBound`, the stretching pairing satisfies
`ω·Sω ≤ C M³` at every point, whenever `|ω(t)|` is bounded. -/
theorem pairing_le_of_periodicStrainLinfBound {ν : ℝ} (hν : 0 < ν) (h : PeriodicStrainLinfBound ν) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
      ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure), IsPeriodicMaximalSolution ν u₀ u p →
        ∀ t : ℝ, 0 ≤ t → (t : EReal) < periodicTstar ν u₀ → ∀ x : T3,
          BddAbove (Set.range fun y => ‖vorticity (u t) y‖) →
          inner ℝ (vorticity (u t) x) (strainAt (u t) x (vorticity (u t) x)) ≤
            C * vorticity_sup_norm (vorticity (u t)) ^ 3 := by
  obtain ⟨C, hC, hb⟩ := h hν
  exact ⟨C, hC, fun u₀ hu₀ u p hm t ht hT x hbdd =>
    pairing_le_of_strain_bound (le_vorticity_sup_norm _ x hbdd) (hb u₀ hu₀ u p hm t ht hT x)⟩

/-- Coined (Nov 2026). **OPEN — never assumed.** The quartic sink: along every smooth maximal
solution, `M(t) = ‖ω(t)‖_∞` is continuous with right derivative `M' ≤ M²(C − κ M)`, `κ > 0`, below
the lifespan. Not derived from the unmodified vorticity equation. -/
def PeriodicQuarticVorticitySink (ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure), IsPeriodicMaximalSolution ν u₀ u p →
      ∃ C κ : ℝ, 0 < κ ∧ ∀ T : ℝ, 0 ≤ T → (T : EReal) < periodicTstar ν u₀ →
        ∃ M' : ℝ → ℝ,
          ContinuousOn (fun t => vorticity_sup_norm (vorticity (u t))) (Icc 0 T) ∧
          ∀ t ∈ Ico 0 T, HasDerivWithinAt (fun t => vorticity_sup_norm (vorticity (u t))) (M' t) (Ici t) t ∧
            M' t ≤ vorticity_sup_norm (vorticity (u t)) ^ 2 *
              (C - κ * vorticity_sup_norm (vorticity (u t)))

/-- **Proved.** The quartic sink would give a ceiling `c` independent of `T`, and a BKM integral
`∫₀ᵀ ‖ω‖_∞ ≤ c T` for every `T` below the lifespan. -/
theorem bkm_bound_of_quarticSink {ν : ℝ} (hν : 0 < ν) (h : PeriodicQuarticVorticitySink ν)
    (u₀ : VelocityField) (hu₀ : IsPeriodicSmoothInitialData u₀) (u : TimeDependentVelocity)
    (p : TimeDependentPressure) (hm : IsPeriodicMaximalSolution ν u₀ u p) :
    ∃ c : ℝ, ∀ T : ℝ, 0 ≤ T → (T : EReal) < periodicTstar ν u₀ →
      (∀ t ∈ Icc 0 T, vorticity_sup_norm (vorticity (u t)) ≤ c) ∧
      IntegrableOn (fun t => vorticity_sup_norm (vorticity (u t))) (Icc 0 T) ∧
      ∫ t in (0:ℝ)..T, vorticity_sup_norm (vorticity (u t)) ≤ c * T := by
  obtain ⟨C, κ, hκ, hT⟩ := h hν u₀ hu₀ u p hm
  set M : ℝ → ℝ := fun t => vorticity_sup_norm (vorticity (u t))
  refine ⟨max (M 0) (C / κ), fun T hT0 hTs => ?_⟩
  obtain ⟨M', hcont, hd⟩ := hT T hT0 hTs
  have hceil := fence_ceiling (M := M) hκ (le_trans (vorticity_sup_norm_nonneg _) (le_max_left _ _))
    (le_max_right _ _) (le_max_left _ _) hcont (fun x hx => (hd x hx).1) (fun x hx => (hd x hx).2)
  exact ⟨hceil, integral_le_of_ceiling hT0 hcont hceil⟩

end PeriodicNSContinuation
