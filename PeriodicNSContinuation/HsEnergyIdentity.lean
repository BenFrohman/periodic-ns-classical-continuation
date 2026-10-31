/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.BKMAssembly

/-!
# Reducing `PeriodicFourierHsEnergyIdentity` (names coined)

**Proved:**
* `hasDerivAt_normSq_complex`: `d/dt ‖z(t)‖² = 2 Re(conj z · z')`.
* `fourierCoeffVF_continuousOn`: each Fourier coefficient of a classical solution is continuous
  in time on `[0, T']` (from joint smoothness; parametric integral over the compact cell).
* `hsSq_hasDerivAt_of_decay`: termwise differentiation of `‖a(t)‖²_{H^s}` given mode-wise
  derivatives and uniform polynomial decay of `a` and `a'`.
* `periodicFourierHsEnergyIdentity_of_coeff`:
  `PeriodicFourierCoeffODE ν → PeriodicFourierCoeffDecay ν → PeriodicFourierHsEnergyIdentity ν s`
  for every real `s`.

**Hypotheses (true, classical, NOT formalized here):**
* `PeriodicFourierCoeffODE ν` — the coefficients of a classical solution satisfy
  `û' = fourierNSField ν û` on `(0, T')` (integrate NS against `e^{-2πik·x}`, differentiate under
  the integral, integrate by parts, Leray-project away the pressure).
* `PeriodicFourierCoeffDecay ν` — uniform-in-time rapid decay of `û(t)` and of
  `fourierNSField ν û(t)` on `[0, T']` (from `(1-Δ)^m` applied to the jointly smooth `u`, `∂ₜu`).
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D TorusFourierNS

namespace PeriodicNSContinuation

/-- **Proved.** Derivative of `‖z(t)‖²` for a complex-valued curve. -/
lemma hasDerivAt_normSq_complex {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun τ => ‖f τ‖ ^ 2) (2 * ((starRingEnd ℂ) (f t) * f').re) t := by
  have hre : HasDerivAt (fun τ => (f τ).re) f'.re t := by
    simpa using (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hf)
  have him : HasDerivAt (fun τ => (f τ).im) f'.im t := by
    simpa using (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hf)
  have h := (hre.pow 2).add (him.pow 2)
  have e : (fun τ => ‖f τ‖ ^ 2) = fun τ => (f τ).re ^ 2 + (f τ).im ^ 2 := by
    funext τ; rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  rw [e]
  convert h using 1
  simp [Complex.mul_re]; ring

/-- Coined. **Hypothesis (true, classical, not formalized).** Fourier coefficient ODE. -/
def PeriodicFourierCoeffODE (ν : ℝ) : Prop :=
  0 < ν → ∀ (u₀ : VelocityField) (u : TimeDependentVelocity) (p : TimeDependentPressure) (T' : ℝ),
    IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T' u p →
    ∀ t ∈ Ioo 0 T', ∀ k i, HasDerivAt (fun τ => fourierCoeffVF (u τ) k i)
      (fourierNSField ν (fourierCoeffVF (u t)) k i) t

/-- Coined. **Hypothesis (true, classical, not formalized).** Uniform rapid decay on `[0,T']`
of the coefficients and of the Fourier NS field evaluated on them. -/
def PeriodicFourierCoeffDecay (ν : ℝ) : Prop :=
  0 < ν → ∀ (u₀ : VelocityField) (u : TimeDependentVelocity) (p : TimeDependentPressure) (T' : ℝ),
    IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T' u p →
    ∀ r : ℝ, ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc 0 T', ∀ k i,
      ‖fourierCoeffVF (u t) k i‖ ≤ B * sobW (-r) k ∧
      ‖fourierNSField ν (fourierCoeffVF (u t)) k i‖ ≤ B * sobW (-r) k

/-- **Proved.** Each Fourier coefficient of a classical solution is continuous on `[0,T']`. -/
theorem fourierCoeffVF_continuousOn {ν : ℝ} {u₀ : VelocityField} {u : TimeDependentVelocity}
    {p : TimeDependentPressure} {T' : ℝ}
    (hsol : IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T' u p) (k : Mode) (i : Fin 3) :
    ContinuousOn (fun t => fourierCoeffVF (u t) k i) (Icc 0 T') := by
  have hT : (0:ℝ) ≤ T' := hsol.1.le
  have hc : ContinuousOn (fun q : ℝ × T3 => u q.1 q.2) (Icc 0 T' ×ˢ univ) :=
    hsol.2.2.2.1.continuousOn
  set pr : ℝ → ℝ := fun t => (projIcc 0 T' hT t : ℝ)
  have hpr : Continuous pr := continuous_subtype_val.comp continuous_projIcc
  have hjoint : Continuous fun q : ℝ × T3 => u (pr q.1) q.2 := by
    refine hc.comp_continuous ((hpr.comp continuous_fst).prodMk continuous_snd) fun q => ?_
    exact ⟨(projIcc 0 T' hT q.1).2, mem_univ _⟩
  set F : ℝ → (Fin 3 → ℝ) → ℂ := fun t x =>
    ((u (pr t) ((EuclideanSpace.equiv (Fin 3) ℝ).symm x) i : ℝ) : ℂ) *
      Complex.exp (-(2 * Real.pi * Complex.I) * ∑ j, ((k j : ℝ) : ℂ) * (x j : ℂ))
  have hF : Continuous (Function.uncurry F) := by
    refine (Complex.continuous_ofReal.comp ((continuous_apply i).comp ?_)).mul ?_
    · exact (PiLp.continuous_ofLp 2 _).comp (hjoint.comp
        (continuous_fst.prodMk ((EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp continuous_snd)))
    · exact Complex.continuous_exp.comp (continuous_const.mul (continuous_finset_sum _ fun j _ =>
        continuous_const.mul (Complex.continuous_ofReal.comp ((continuous_apply j).comp continuous_snd))))
  have hint : Continuous fun t => ∫ x in Icc (0 : Fin 3 → ℝ) 1, F t x :=
    continuous_parametric_integral_of_continuous hF isCompact_Icc
  refine hint.continuousOn.congr fun t ht => ?_
  simp only [fourierCoeffVF, F, pr, projIcc_of_mem hT ht]

/-- Coined. Unsquared `H^s` sum. -/
lemma hsSq_eq_tsum (s : ℝ) (v : VelocityField) :
    hsSq s v = ∑' p : Mode × Fin 3, sobW s p.1 * ‖fourierCoeffVF v p.1 p.2‖ ^ 2 := by
  unfold hsSq hsNormField
  exact Real.sq_sqrt (tsum_nonneg fun p => mul_nonneg (sobW_pos s p.1).le (sq_nonneg _))

/-- **Proved.** A mode-only weight is summable over `Mode × Fin 3` if it is over `Mode`. -/
lemma summable_prod_fin3 {c : Mode → ℝ} (hc0 : ∀ k, 0 ≤ c k) (hc : Summable c) :
    Summable fun p : Mode × Fin 3 => c p.1 := by
  refine (summable_prod_of_nonneg fun p => hc0 p.1).2 ⟨fun _ => Summable.of_finite, ?_⟩
  simpa using hc.mul_left 3

lemma sobW_mul_sobW (a b : ℝ) (k : Mode) : sobW a k * sobW b k = sobW (a + b) k := by
  unfold sobW; rw [← Real.rpow_add (one_add_sq_pos k)]

/-- **Proved.** The rate terms are dominated by `2B² ⟨k⟩^{2(s-2r)}`. -/
lemma rate_term_le {s r B : ℝ} {x y : ℂ} {k : Mode} (hx : ‖x‖ ≤ B * sobW (-r) k)
    (hy : ‖y‖ ≤ B * sobW (-r) k) :
    ‖sobW s k * (2 * ((starRingEnd ℂ) x * y).re)‖ ≤ 2 * B ^ 2 * sobW (s + -r + -r) k := by
  have hw := (sobW_pos s k).le
  have h1 : |((starRingEnd ℂ) x * y).re| ≤ ‖x‖ * ‖y‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_; simp
  have hB : ‖x‖ * ‖y‖ ≤ (B * sobW (-r) k) * (B * sobW (-r) k) :=
    mul_le_mul hx hy (norm_nonneg _) ((norm_nonneg _).trans hx)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw, abs_mul, abs_two, ← sobW_mul_sobW,
    ← sobW_mul_sobW]
  have := mul_le_mul_of_nonneg_left (h1.trans hB) hw
  nlinarith

lemma sq_term_le {s r B : ℝ} {x : ℂ} {k : Mode} (hx : ‖x‖ ≤ B * sobW (-r) k) :
    ‖sobW s k * ‖x‖ ^ 2‖ ≤ 2 * B ^ 2 * sobW (s + -r + -r) k := by
  have hw := (sobW_pos s k).le
  have h0 : 0 ≤ B * sobW (-r) k := (norm_nonneg _).trans hx
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← sobW_mul_sobW, ← sobW_mul_sobW]
  have h2 : ‖x‖ ^ 2 ≤ (B * sobW (-r) k) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
  have := mul_le_mul_of_nonneg_left h2 hw
  nlinarith [sq_nonneg (B * sobW (-r) k), mul_nonneg hw (sq_nonneg (B * sobW (-r) k))]

/-- **Proved.** `PeriodicFourierHsEnergyIdentity ν s` for every real `s`, from the coefficient ODE
and uniform decay. -/
theorem periodicFourierHsEnergyIdentity_of_coeff {ν : ℝ} (s : ℝ)
    (hODE : PeriodicFourierCoeffODE ν) (hD : PeriodicFourierCoeffDecay ν) :
    PeriodicFourierHsEnergyIdentity ν s := by
  intro hν u₀ u p T' hsol
  set r : ℝ := |s| + 2
  obtain ⟨B, hB0, hB⟩ := hD hν u₀ u p T' hsol r
  have hσ : 3 / 2 < -(s + -r + -r) := by
    have := le_abs_self s; have := abs_nonneg s; simp only [r]; linarith
  have hsum0 : Summable fun k : Mode => 2 * B ^ 2 * sobW (s + -r + -r) k := by
    have := (summable_sobW_neg hσ).mul_left (2 * B ^ 2)
    simpa using this
  have hU : Summable fun q : Mode × Fin 3 => 2 * B ^ 2 * sobW (s + -r + -r) q.1 :=
    summable_prod_fin3 (fun k => by have := sobW_pos (s + -r + -r) k; positivity) hsum0
  set a : ℝ → Mode × Fin 3 → ℂ := fun t q => fourierCoeffVF (u t) q.1 q.2
  have hcont : ContinuousOn (fun t => hsSq s (u t)) (Icc 0 T') := by
    simp_rw [hsSq_eq_tsum]
    refine continuousOn_tsum (fun q => ?_) hU fun q t ht => sq_term_le (hB t ht q.1 q.2).1
    exact continuousOn_const.mul ((fourierCoeffVF_continuousOn hsol q.1 q.2).norm.pow 2)
  refine ⟨hcont, fun t ht => ⟨?_, ?_⟩⟩
  · exact Summable.of_norm_bounded hU fun q =>
      rate_term_le (hB t (Ioo_subset_Icc_self ht) q.1 q.2).1 (hB t (Ioo_subset_Icc_self ht) q.1 q.2).2
  · have hd := hasDerivAt_tsum_of_isPreconnected (g := fun (q : Mode × Fin 3) τ =>
        sobW s q.1 * ‖fourierCoeffVF (u τ) q.1 q.2‖ ^ 2)
      (g' := fun q τ => sobW s q.1 * (2 * ((starRingEnd ℂ) (fourierCoeffVF (u τ) q.1 q.2) *
        fourierNSField ν (fourierCoeffVF (u τ)) q.1 q.2).re))
      hU isOpen_Ioo isPreconnected_Ioo
      (fun q y hy => (hasDerivAt_normSq_complex (hODE hν u₀ u p T' hsol y hy q.1 q.2)).const_mul _)
      (fun q y hy => rate_term_le (hB y (Ioo_subset_Icc_self hy) q.1 q.2).1
        (hB y (Ioo_subset_Icc_self hy) q.1 q.2).2) ht
      (Summable.of_norm_bounded hU fun q => sq_term_le (hB t (Ioo_subset_Icc_self ht) q.1 q.2).1) ht
    simp_rw [hsSq_eq_tsum]
    exact hd

/-- **Proved (conditional).** BKM `H^s` control with the energy identity replaced by the
coefficient ODE and decay Props. -/
theorem periodicBKMHsControl_of_coeff_lowFreq {s : ℝ} (ν : ℝ) (hs : 5 / 2 < s)
    (hODE : ∀ ν, PeriodicFourierCoeffODE ν) (hD : ∀ ν, PeriodicFourierCoeffDecay ν)
    (hC : ∃ C, 0 ≤ C ∧ PeriodicFourierCommutatorBound s C)
    (hL : PeriodicLowFreqVorticityBound) : PeriodicBKMHsControl ν s :=
  periodicBKMHsControl_of_fourier_lowFreq ν hs
    (fun ν => periodicFourierHsEnergyIdentity_of_coeff s (hODE ν) (hD ν)) hC hL

end PeriodicNSContinuation
