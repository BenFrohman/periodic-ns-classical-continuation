/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.ClassicalSteps
import PeriodicNSContinuation.EnstrophyRate

/-!
# Energy equality and the time integrability of the enstrophy on `𝕋³`

Work in progress. **Nothing here proves `PeriodicBKMIntegrability` or Clay (B).**

* `PeriodicNonlinearEnergyCancellation` — coined, **OPEN here (classical, not formalized)**:
  the Fourier form of `⟨(u·∇)u, u⟩_{L²} = 0` for smooth divergence-free periodic `u`
  (Leray 1934; Temam, *Navier–Stokes Equations* (1977), Ch. II, Lemma 1.3; Robinson–Rodrigo–
  Sadowski, *The Three-Dimensional Navier–Stokes Equations* (2016), Ch. 3).
* `energy_hasDerivAt` — **proved**: the energy equality
  `d/dt ‖u‖²_{L²} = −8π²ν (‖u‖²_{H¹} − ‖u‖²_{L²})` on `(0,T)`.
* `periodicEnstrophyTimeIntegrable_of_cancellation` — **proved**:
  `PeriodicNonlinearEnergyCancellation → PeriodicEnstrophyTimeIntegrable ν`. The primitive is
  `G(t) = ∫₀ᵗ E − E(t)/(8π²ν)` with `E` extended to `t = T` by its (monotone) left limit.
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D TorusFourierNS

namespace PeriodicNSContinuation

open Corrected

/-- Coined. **Hypothesis (OPEN here; classical: `⟨(u·∇)u, u⟩ = 0`, Leray 1934, Temam 1977
Ch. II Lemma 1.3; not formalized on the Fourier side).** -/
def PeriodicNonlinearEnergyCancellation : Prop :=
  ∀ v : VelocityField, IsPeriodicSmoothInitialData v →
    Summable (fun p : Mode × Fin 3 => sobW 0 p.1 *
        (2 * ((starRingEnd ℂ) (fourierCoeffVF v p.1 p.2) * nlField (fourierCoeffVF v) p.1 p.2).re)) ∧
    rateOf 0 (nlField (fourierCoeffVF v)) (fourierCoeffVF v) = 0

lemma sobW_zero_eq (k : Mode) : sobW 0 k = 1 := by simp [sobW]

/-- `H^s` summability on a solution interval, from the proved coefficient decay. -/
lemma hs_summable_of_sol {ν : ℝ} (hν : 0 < ν) {u₀ : VelocityField} {u : TimeDependentVelocity}
    {p : TimeDependentPressure} {T' : ℝ} (hsol : IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T' u p)
    (s : ℝ) {t : ℝ} (ht : t ∈ Icc 0 T') :
    Summable fun q : Mode × Fin 3 => sobW s q.1 * ‖fourierCoeffVF (u t) q.1 q.2‖ ^ 2 := by
  set r : ℝ := |s| + 2
  obtain ⟨B, -, hB⟩ := periodicFourierCoeffDecay ν hν u₀ u p T' hsol r
  have hσ : 3 / 2 < -(s + -r + -r) := by
    have := le_abs_self s; have := abs_nonneg s; simp only [r]; linarith
  have hsum0 : Summable fun k : Mode => 2 * B ^ 2 * sobW (s + -r + -r) k := by
    simpa using (summable_sobW_neg hσ).mul_left (2 * B ^ 2)
  have hU := summable_prod_fin3 (fun k => by have := sobW_pos (s + -r + -r) k; positivity) hsum0
  exact Summable.of_norm_bounded hU fun q => sq_term_le (s := s) (hB t ht q.1 q.2).1

/-- **Proved (from the cancellation Prop).** Energy equality on a solution interval. -/
theorem energy_hasDerivAt (hC : PeriodicNonlinearEnergyCancellation) {ν : ℝ} (hν : 0 < ν)
    {u₀ : VelocityField} {u : TimeDependentVelocity} {p : TimeDependentPressure} {T' : ℝ}
    (hsol : IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T' u p) {t : ℝ} (ht : t ∈ Ioo 0 T') :
    HasDerivAt (fun t => hsSq 0 (u t))
      (-(8 * Real.pi ^ 2 * ν) * (h1Sq (u t) - hsSq 0 (u t))) t := by
  have htI : t ∈ Icc (0:ℝ) T' := Ioo_subset_Icc_self ht
  have hut : IsPeriodicSmoothInitialData (u t) :=
    ⟨contDiff_slice hsol.2.2.2.1 htI, fun z => hsol.2.2.2.2.2.2.1 t htI z, hsol.2.1 t htI⟩
  obtain ⟨hnl, hnl0⟩ := hC (u t) hut
  obtain ⟨-, hder⟩ := periodicFourierHsEnergyIdentity ν 0 hν u₀ u p T' hsol
  obtain ⟨hsum, hd⟩ := hder t ht
  set a := fourierCoeffVF (u t)
  have hsplit : ∀ q : Mode × Fin 3, sobW 0 q.1 *
      (2 * ((starRingEnd ℂ) (a q.1 q.2) * fourierNSField ν a q.1 q.2).re) =
      sobW 0 q.1 * (2 * ((starRingEnd ℂ) (a q.1 q.2) * (-((viscCoeff ν q.1 : ℝ) : ℂ) * a q.1 q.2)).re)
      + sobW 0 q.1 * (2 * ((starRingEnd ℂ) (a q.1 q.2) * nlField a q.1 q.2).re) := fun q => by
    rw [fourierNSField_eq, mul_add, Complex.add_re]; ring
  have hvs : Summable fun q : Mode × Fin 3 => sobW 0 q.1 *
      (2 * ((starRingEnd ℂ) (a q.1 q.2) * (-((viscCoeff ν q.1 : ℝ) : ℂ) * a q.1 q.2)).re) := by
    refine (hsum.sub hnl).congr fun q => ?_
    simp only [hsplit]; ring
  have hterm : ∀ q : Mode × Fin 3, sobW 0 q.1 *
      (2 * ((starRingEnd ℂ) (a q.1 q.2) * (-((viscCoeff ν q.1 : ℝ) : ℂ) * a q.1 q.2)).re) =
      -(8 * Real.pi ^ 2 * ν) * (sobW 1 q.1 * ‖a q.1 q.2‖ ^ 2 - sobW 0 q.1 * ‖a q.1 q.2‖ ^ 2) := by
    intro q
    have : ((starRingEnd ℂ) (a q.1 q.2) * (-((viscCoeff ν q.1 : ℝ) : ℂ) * a q.1 q.2)).re =
        -(viscCoeff ν q.1 * ‖a q.1 q.2‖ ^ 2) := by
      rw [show (starRingEnd ℂ) (a q.1 q.2) * (-((viscCoeff ν q.1 : ℝ) : ℂ) * a q.1 q.2) =
          -((viscCoeff ν q.1 : ℝ) : ℂ) * ((starRingEnd ℂ) (a q.1 q.2) * a q.1 q.2) by ring,
        Complex.conj_mul']
      simp [← Complex.ofReal_pow]
    rw [this, sobW_zero_eq, sobW_one_eq]; unfold viscCoeff; ring
  have h1s := hs_summable_of_sol hν hsol 1 htI
  have h0s := hs_summable_of_sol hν hsol 0 htI
  have hrate : rateOf 0 (fourierNSField ν a) a =
      -(8 * Real.pi ^ 2 * ν) * (h1Sq (u t) - hsSq 0 (u t)) := by
    unfold rateOf
    rw [tsum_congr hsplit, hvs.tsum_add hnl]
    have := hnl0; unfold rateOf at this; rw [this, add_zero, tsum_congr hterm, tsum_mul_left,
      h1s.tsum_sub h0s, h1Sq, hsSq_eq_tsum, hsSq_eq_tsum]
  rw [← hrate]; exact hd

/-- **Proved.** `PeriodicEnstrophyTimeIntegrable` from the energy cancellation. -/
theorem periodicEnstrophyTimeIntegrable_of_cancellation (hC : PeriodicNonlinearEnergyCancellation)
    (ν : ℝ) : PeriodicEnstrophyTimeIntegrable ν := by
  intro hν u₀ hu₀ u p hm T hT
  have hTpos : 0 < T := by
    have := periodicLocalExistence_of_nonneg hν.le hν u₀ hu₀
    rw [hT] at this; exact_mod_cast this
  set E : ℝ → ℝ := fun t => hsSq 0 (u t) with hE
  set c : ℝ := 8 * Real.pi ^ 2 * ν with hc
  have hcpos : 0 < c := by positivity
  -- derivative on (0,T)
  have hder : ∀ t ∈ Ioo (0:ℝ) T, HasDerivAt E (-c * (h1Sq (u t) - E t)) t := by
    intro t ht
    obtain ⟨hsol, -, hle⟩ := sol_around hm hT ⟨ht.1.le, ht.2⟩
    exact energy_hasDerivAt hC hν hsol ⟨ht.1, by linarith [ht.2]⟩
  -- continuity of E within [0,T] at points of [0,T)
  have hcw : ∀ t ∈ Ico (0:ℝ) T, ContinuousWithinAt E (Icc 0 T) t := by
    intro t ht
    obtain ⟨hsol, htm, hle⟩ := sol_around hm hT ht
    obtain ⟨hc0, -⟩ := periodicFourierHsEnergyIdentity ν 0 hν u₀ u p _ hsol
    have hmem : Icc (0:ℝ) ((t + T) / 2) ∈ 𝓝[Icc 0 T] t := by
      refine mem_nhdsWithin.2 ⟨Iio ((t + T) / 2), isOpen_Iio, by simp; linarith [ht.2],
        fun x hx => ⟨hx.2.1, le_of_lt hx.1⟩⟩
    exact ((hc0 t htm).mono_of_mem_nhdsWithin hmem)
  have hgap : ∀ t ∈ Ioo (0:ℝ) T, E t ≤ h1Sq (u t) := by
    intro t ht
    obtain ⟨hsol, htm, -⟩ := sol_around hm hT ⟨ht.1.le, ht.2⟩
    show hsSq 0 (u t) ≤ hsSq 1 (u t)
    rw [hsSq_eq_tsum, hsSq_eq_tsum]
    refine Summable.tsum_le_tsum (fun q => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
      (hs_summable_of_sol hν hsol 0 htm) (hs_summable_of_sol hν hsol 1 htm)
    rw [sobW_zero_eq, sobW_one_eq]; have : 0 ≤ ksq (kvec q.1) := by unfold ksq; positivity
    linarith
  have hanti : AntitoneOn E (Ico 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ico 0 T)
      (fun t ht => (hcw t ht).mono Ico_subset_Icc_self)
    · intro x hx; rw [interior_Ico] at hx; exact (hder x hx).differentiableAt.differentiableWithinAt
    · intro x hx; rw [interior_Ico] at hx; rw [(hder x hx).deriv]
      have := hgap x hx; nlinarith
  -- monotone extension
  set g0 : ℝ → ℝ := fun t => E (max t 0) with hg0
  set L : ℝ := sInf (g0 '' Iio T) with hL
  set g : ℝ → ℝ := fun t => if t < T then g0 t else L with hg
  have hbdd : BddBelow (g0 '' Iio T) := ⟨0, by rintro _ ⟨x, -, rfl⟩; exact hsSq_nonneg 0 _⟩
  have hgA : Antitone g := by
    intro x y hxy
    simp only [hg]
    by_cases hy : y < T
    · have hx : x < T := lt_of_le_of_lt hxy hy
      simp only [hx, hy, if_true, hg0]
      exact hanti ⟨le_max_right _ _, max_lt hx hTpos⟩ ⟨le_max_right _ _, max_lt hy hTpos⟩
        (max_le_max hxy le_rfl)
    · simp only [hy, if_false]
      by_cases hx : x < T
      · simp only [hx, if_true]; exact csInf_le hbdd ⟨x, hx, rfl⟩
      · simp [hx]
  have hgE : ∀ t ∈ Ico (0:ℝ) T, g t = E t := by
    intro t ht; simp [hg, hg0, ht.2, max_eq_left ht.1]
  have hgcont : ContinuousOn g (Icc 0 T) := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with htT | htT
    · subst htT
      have hlim := hgA.tendsto_nhdsLT t
      have him : g '' Iio t = g0 '' Iio t := by
        ext y; constructor
        · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by simp [hg, show x < t from hx]⟩
        · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by simp [hg, show x < t from hx]⟩
      have hgt : g t = L := by simp [hg]
      rw [him, ← hL, ← hgt] at hlim
      have : ContinuousWithinAt g (Iic t) t := continuousWithinAt_Iio_iff_Iic.1 hlim
      exact this.mono fun x hx => hx.2
    · have h1 := hcw t ⟨ht.1, htT⟩
      refine (h1.congr_of_eventuallyEq ?_ (hgE t ⟨ht.1, htT⟩))
      have hmem : Icc (0:ℝ) T ∩ Iio T ∈ 𝓝[Icc 0 T] t :=
        inter_mem_nhdsWithin _ (Iio_mem_nhds htT)
      filter_upwards [hmem] with x hx using hgE x ⟨hx.1.1, hx.2⟩
  have hint : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
    (hgA.antitoneOn _).intervalIntegrable
  refine ⟨fun t => (∫ s in (0:ℝ)..t, g s) - g t / c, ?_, ?_⟩
  · exact ((intervalIntegral.continuous_primitive hint 0).continuousOn).sub
      (hgcont.div_const c)
  · intro t ht
    have hev : g =ᶠ[𝓝 t] E := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx using hgE x ⟨hx.1.le, hx.2⟩
    have hgd : HasDerivAt g (-c * (h1Sq (u t) - E t)) t :=
      (hder t ht).congr_of_eventuallyEq hev
    have hgc : ContinuousAt g t := hgd.continuousAt
    have hI := intervalIntegral.integral_hasDerivAt_right (hint 0 t)
      (hgA.measurable.stronglyMeasurable.stronglyMeasurableAtFilter) hgc
    have := hI.sub (hgd.div_const c)
    convert this using 1
    rw [hgE t ⟨ht.1.le, ht.2⟩]; field_simp; ring

/-! ## Standard form of the `H¹ → H²` smoothing step

The Prop `PeriodicH2SmoothingRate` (ClassicalSteps.lean) asks for a rate *linear* in
`‖u‖²_{H²}` with an `H¹`-only coefficient. The standard 3D estimate (Temam, *Navier–Stokes
Equations and Nonlinear Functional Analysis*, 2nd ed. 1995, §4; Robinson–Rodrigo–Sadowski 2016,
Ch. 7) is instead, after absorbing the viscous `H³` term,
`d/dt ‖Δu‖² ≤ (C/ν) ‖∇u‖ ‖Δu‖ · ‖Δu‖²`, i.e. the coefficient carries one extra factor
`‖u‖_{H²}`, and closes by Grönwall because `∫₀ᵀ ‖Δu‖² < ∞` when `‖∇u‖` is bounded. The two Props
below record that standard form; the theorem after them proves Leray's criterion from them.
-/

/-- Coined. **Hypothesis (OPEN here; classical `H²` estimate in the standard form, Temam 1995 §4,
Robinson–Rodrigo–Sadowski 2016 Ch. 7; not formalized).** -/
def PeriodicH2SmoothingRateStd (ν : ℝ) : Prop :=
  ∃ K m : ℝ, ∀ v : VelocityField, IsPeriodicSmoothInitialData v →
    rateOf 2 (fourierNSField ν (fourierCoeffVF v)) (fourierCoeffVF v) ≤
      K * (1 + h1Sq v) ^ m * (Real.sqrt (hsSq 2 v) * hsSq 2 v)

/-- Coined. **Hypothesis (OPEN here; classical: bounded enstrophy gives `∫₀ᵀ ‖Δu‖² < ∞`, hence
`∫₀ᵀ ‖u‖_{H²} < ∞`; Temam 1995 §4, Robinson–Rodrigo–Sadowski 2016 Ch. 6–7; not formalized).** -/
def PeriodicH2RootTimeIntegrable (ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure), IsPeriodicMaximalSolution ν u₀ u p →
      ∀ T : ℝ, periodicTstar ν u₀ = (T : EReal) → (∃ M : ℝ, ∀ t ∈ Ico (0:ℝ) T, h1Sq (u t) ≤ M) →
        ∃ G : ℝ → ℝ, ContinuousOn G (Icc 0 T) ∧
          ∀ t ∈ Ioo (0:ℝ) T, HasDerivAt G (Real.sqrt (hsSq 2 (u t))) t

/-- **Proved.** Leray's criterion from the standard-form `H²` step, the `H²` time integrability,
and the `H³` step, via the proved integrating-factor Grönwall and `H³` blow-up alternative. -/
theorem periodicH1BlowupCriterion_of_smoothingStd {ν : ℝ} (h2 : PeriodicH2SmoothingRateStd ν)
    (hI : PeriodicH2RootTimeIntegrable ν) (h3 : PeriodicH3SmoothingRate ν) :
    PeriodicH1BlowupCriterion ν := by
  intro hν u₀ hu₀ u p hm T hT ⟨M, hM⟩
  obtain ⟨K2, m2, hK2⟩ := h2
  obtain ⟨K3, m3, hK3⟩ := h3
  obtain ⟨G, hGc, hGd⟩ := hI hν u₀ hu₀ u p hm T hT ⟨M, hM⟩
  have hdata : ∀ t ∈ Ioo (0:ℝ) T, IsPeriodicSmoothInitialData (u t) :=
    fun t ht => slice_data hm hT ⟨ht.1.le, ht.2⟩
  have hTpos : 0 < T := by
    have := periodicLocalExistence_of_nonneg hν.le hν u₀ hu₀
    rw [hT] at this; exact_mod_cast this
  have hM0 : 0 ≤ M := (hsSq_nonneg 1 (u 0)).trans (hM 0 ⟨le_rfl, hTpos⟩)
  obtain ⟨A2, hA2⟩ := rpow_coeff_bound (K := K2) (m := m2) hM0
  have hrate : ∀ t ∈ Ioo (0:ℝ) T,
      rateOf 2 (fourierNSField ν (fourierCoeffVF (u t))) (fourierCoeffVF (u t)) ≤
        (A2 * Real.sqrt (hsSq 2 (u t))) * hsSq 2 (u t) := fun t ht => by
    have := (hK2 _ (hdata t ht)).trans (hA2 _ (hsSq_nonneg 1 _) (hM t ⟨ht.1.le, ht.2⟩) _
      (mul_nonneg (Real.sqrt_nonneg _) (hsSq_nonneg 2 _)))
    linarith [mul_assoc A2 (Real.sqrt (hsSq 2 (u t))) (hsSq 2 (u t))]
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn hGc
  have hM2 : ∀ t ∈ Ico (0:ℝ) T, hsSq 2 (u t) ≤ hsSq 2 u₀ * Real.exp (2 * |A2| * B) := by
    intro t ht
    obtain ⟨hsol, htm, hle⟩ := sol_around hm hT ht
    obtain ⟨hc, hd⟩ := periodicFourierHsEnergyIdentity ν 2 hν u₀ u p _ hsol
    have hu0 : u 0 = u₀ := u_zero hsol
    have hsub : Icc (0:ℝ) ((t + T) / 2) ⊆ Icc 0 T := Icc_subset_Icc le_rfl hle
    have hsubo : ∀ x ∈ Ioo (0:ℝ) ((t + T) / 2), x ∈ Ioo (0:ℝ) T :=
      fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hle⟩
    have key := gronwall_integrating_factor (f := fun t => hsSq 2 (u t))
      (g := fun t => A2 * Real.sqrt (hsSq 2 (u t))) (G := fun t => A2 * G t) hc
      ((continuousOn_const.mul hGc).mono hsub) (fun x hx => (hd x hx).2)
      (fun x hx => (hGd x (hsubo x hx)).const_mul A2) (fun x hx => hrate x (hsubo x hx)) t htm
    simp only [hu0] at key
    refine key.trans (mul_le_mul_of_nonneg_left ?_ (hsSq_nonneg 2 u₀))
    apply Real.exp_le_exp.2
    have h1 := abs_le.1 (hB t (hsub htm))
    have h2 := abs_le.1 (hB 0 (hsub ⟨le_rfl, htm.1.trans htm.2⟩))
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 ⟨le_rfl, hTpos.le⟩)
    rw [← mul_sub]
    calc A2 * (G t - G 0) ≤ |A2 * (G t - G 0)| := le_abs_self _
      _ = |A2| * |G t - G 0| := abs_mul _ _
      _ ≤ |A2| * (2 * B) := mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith, by linarith⟩)
          (abs_nonneg _)
      _ = 2 * |A2| * B := by ring
  set M2 := hsSq 2 u₀ * Real.exp (2 * |A2| * B)
  have hM20 : 0 ≤ M2 := (hsSq_nonneg 2 (u 0)).trans (hM2 0 ⟨le_rfl, hTpos⟩)
  obtain ⟨A3, hA3⟩ := rpow_coeff_bound (K := K3) (m := m3) hM20
  obtain ⟨M3, hM3⟩ := hsSq_bounded_of_rate (s := 3) (A := A3) hν hm hT fun t ht =>
    (hK3 _ (hdata t ht)).trans (hA3 _ (hsSq_nonneg 2 _) (hM2 t ⟨ht.1.le, ht.2⟩) _
      (hsSq_nonneg 3 _))
  exact periodicHsBlowupAlternative hν.le (by norm_num) hν u₀ hu₀ u p hm T hT
    ⟨Real.sqrt M3, fun t ht => hsNorm_le_of_hsSq_le (hM3 t ht)⟩

/-- **Proved (conditional).** `PeriodicBKMIntegrability` from the standard-form classical Props,
the energy cancellation, and the OPEN hidden property. -/
theorem periodicBKMIntegrability_of_classical_bending_std {ν : ℝ}
    (hS : PeriodicHolderStretchingEstimate ν) (hC : PeriodicNonlinearEnergyCancellation)
    (h2 : PeriodicH2SmoothingRateStd ν) (hI : PeriodicH2RootTimeIntegrable ν)
    (h3 : PeriodicH3SmoothingRate ν) (hB : PeriodicBendingRateHiddenProperty ν) :
    PeriodicBKMIntegrability ν :=
  periodicBKMIntegrability_of_bending
    (periodicDirectionEnstrophyGrowthL1_of_holderStretching hS
      (periodicEnstrophyTimeIntegrable_of_cancellation hC ν))
    (periodicH1BlowupCriterion_of_smoothingStd h2 hI h3) hB

end PeriodicNSContinuation
