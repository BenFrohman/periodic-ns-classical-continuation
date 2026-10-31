/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.BendingRate

/-!
# Breaking down Leray's `H¹` criterion and the analytic Constantin–Fefferman step

Work in progress. **Nothing here proves `PeriodicBKMIntegrability` or Clay (B).**

## Leray's criterion (`PeriodicH1BlowupCriterion`)
Route: parabolic smoothing `H¹ → H² → H³`, then the **proved** `H³` blow-up alternative
`periodicHsBlowupAlternative` (s = 3) and the **proved** `H^s` energy identity
`periodicFourierHsEnergyIdentity`.
* `hsSq_bounded_of_rate` — **proved**: on a maximal solution, a rate bound
  `d/dt ‖u‖²_{H^s} ≤ A ‖u‖²_{H^s}` on `(0,T)` bounds `‖u‖²_{H^s}` on `[0,T)`.
* `PeriodicH2SmoothingRate ν` — **OPEN (classical, Temam / Constantin–Foias; not formalized)**:
  `rateOf 2 ≤ K (1 + ‖u‖²_{H¹})^m ‖u‖²_{H²}` (viscous term absorbing the trilinear term).
* `PeriodicH3SmoothingRate ν` — **OPEN (classical, not formalized)**:
  `rateOf 3 ≤ K (1 + ‖u‖²_{H²})^m ‖u‖²_{H³}`.
* `periodicH1BlowupCriterion_of_smoothing` — **proved**: the two rate Props ⇒
  `PeriodicH1BlowupCriterion`.

## Analytic Constantin–Fefferman / Beirão da Veiga–Berselli step
* `PeriodicHolderStretchingEstimate ν` — **OPEN (CF 1993 Biot–Savart stretching representation on
  `T³` + BdV–B 2002 interpolation; not formalized)**: under `VortDirHolderHalf`,
  `rateOf 1 ≤ K ‖u‖²_{H¹} · ‖u‖²_{H¹}`, i.e. rate `g = K ‖u‖²_{H¹}` times enstrophy.
* `PeriodicEnstrophyTimeIntegrable ν` — **OPEN here (classical: energy equality gives
  `∫₀^T ‖∇u‖² ≤ ‖u₀‖²/(2ν)`)**: `t ↦ ‖u(t)‖²_{H¹}` has a primitive continuous on `[0,T]`.
* `periodicDirectionEnstrophyGrowthL1_of_holderStretching` — **proved**: the two ⇒
  `PeriodicDirectionEnstrophyGrowthL1`.
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D

namespace PeriodicNSContinuation

open Corrected

/-- **Proved.** A linear rate bound for `‖u‖²_{H^s}` on `(0,T)` bounds it on `[0,T)`. -/
theorem hsSq_bounded_of_rate {ν s A : ℝ} (hν : 0 < ν) {u₀ : VelocityField}
    {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (hm : IsPeriodicMaximalSolution ν u₀ u p) {T : ℝ} (hT : periodicTstar ν u₀ = (T : EReal))
    (hA : ∀ t ∈ Ioo (0:ℝ) T,
      rateOf s (fourierNSField ν (fourierCoeffVF (u t))) (fourierCoeffVF (u t)) ≤
        A * hsSq s (u t)) :
    ∃ M : ℝ, ∀ t ∈ Ico (0:ℝ) T, hsSq s (u t) ≤ M := by
  refine ⟨hsSq s u₀ * Real.exp (max A 0 * T), fun t ht => ?_⟩
  obtain ⟨hsol, htm, hle⟩ := sol_around hm hT ht
  obtain ⟨hc, hd⟩ := periodicFourierHsEnergyIdentity ν s hν u₀ u p _ hsol
  have hu0 : u 0 = u₀ := u_zero hsol
  have key := exp_gronwall_Ioo (f := fun t => hsSq s (u t)) (A := max A 0) hc
    (fun x hx => (hd x hx).2) (fun x hx => by
      have h1 := hA x ⟨hx.1, lt_of_lt_of_le hx.2 hle⟩
      exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left A 0) (hsSq_nonneg s (u x)))) t htm
  simp only [hu0] at key
  refine key.trans (mul_le_mul_of_nonneg_left ?_ (hsSq_nonneg s u₀))
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2.le (le_max_right A 0))

/-- Coined. **Hypothesis (OPEN here; classical `H¹ → H²` parabolic smoothing, not formalized).** -/
def PeriodicH2SmoothingRate (ν : ℝ) : Prop :=
  ∃ K m : ℝ, ∀ v : VelocityField, IsPeriodicSmoothInitialData v →
    rateOf 2 (fourierNSField ν (fourierCoeffVF v)) (fourierCoeffVF v) ≤
      K * (1 + h1Sq v) ^ m * hsSq 2 v

/-- Coined. **Hypothesis (OPEN here; classical `H² → H³` smoothing, not formalized).** -/
def PeriodicH3SmoothingRate (ν : ℝ) : Prop :=
  ∃ K m : ℝ, ∀ v : VelocityField, IsPeriodicSmoothInitialData v →
    rateOf 3 (fourierNSField ν (fourierCoeffVF v)) (fourierCoeffVF v) ≤
      K * (1 + hsSq 2 v) ^ m * hsSq 3 v

/-- Slices of a maximal solution are smooth periodic initial data. -/
lemma slice_data {ν : ℝ} {u₀ : VelocityField} {u : TimeDependentVelocity}
    {p : TimeDependentPressure} (hm : IsPeriodicMaximalSolution ν u₀ u p) {T : ℝ}
    (hT : periodicTstar ν u₀ = (T : EReal)) {t : ℝ} (ht : t ∈ Ico (0:ℝ) T) :
    IsPeriodicSmoothInitialData (u t) := by
  obtain ⟨hsol, htm, -⟩ := sol_around hm hT ht
  exact ⟨contDiff_slice hsol.2.2.2.1 htm, fun x => hsol.2.2.2.2.2.2.1 t htm x, hsol.2.1 t htm⟩

/-- Bounded coefficient: `(1+X)^m ≤ B` when `0 ≤ X ≤ M`. -/
lemma rpow_coeff_bound {K m M : ℝ} (hM : 0 ≤ M) :
    ∃ A : ℝ, ∀ X : ℝ, 0 ≤ X → X ≤ M → ∀ Y : ℝ, 0 ≤ Y → K * (1 + X) ^ m * Y ≤ A * Y := by
  refine ⟨|K| * max ((1 + M) ^ m) 1, fun X hX hXM Y hY => ?_⟩
  apply mul_le_mul_of_nonneg_right _ hY
  have h1 : (1 + X) ^ m ≤ max ((1 + M) ^ m) 1 := by
    rcases le_total 0 m with hm | hm
    · exact (Real.rpow_le_rpow (by linarith) (by linarith) hm).trans (le_max_left _ _)
    · exact (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) hm).trans (le_max_right _ _)
  have h0 : 0 ≤ (1 + X) ^ m := Real.rpow_nonneg (by linarith) m
  calc K * (1 + X) ^ m ≤ |K| * (1 + X) ^ m := mul_le_mul_of_nonneg_right (le_abs_self K) h0
    _ ≤ |K| * max ((1 + M) ^ m) 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg K)

/-- **Proved.** Leray's criterion from the two smoothing rates and the proved `H³` blow-up
alternative. -/
theorem periodicH1BlowupCriterion_of_smoothing {ν : ℝ} (h2 : PeriodicH2SmoothingRate ν)
    (h3 : PeriodicH3SmoothingRate ν) : PeriodicH1BlowupCriterion ν := by
  intro hν u₀ hu₀ u p hm T hT ⟨M, hM⟩
  obtain ⟨K2, m2, hK2⟩ := h2
  obtain ⟨K3, m3, hK3⟩ := h3
  have hdata : ∀ t ∈ Ioo (0:ℝ) T, IsPeriodicSmoothInitialData (u t) :=
    fun t ht => slice_data hm hT ⟨ht.1.le, ht.2⟩
  have hTpos : 0 < T := by
    have := periodicLocalExistence_of_nonneg hν.le hν u₀ hu₀
    rw [hT] at this; exact_mod_cast this
  have hM0 : 0 ≤ M := (hsSq_nonneg 1 (u 0)).trans (hM 0 ⟨le_rfl, hTpos⟩)
  obtain ⟨A2, hA2⟩ := rpow_coeff_bound (K := K2) (m := m2) hM0
  obtain ⟨M2, hM2⟩ := hsSq_bounded_of_rate (s := 2) (A := A2) hν hm hT fun t ht =>
    (hK2 _ (hdata t ht)).trans (hA2 _ (hsSq_nonneg 1 _) (hM t ⟨ht.1.le, ht.2⟩) _
      (hsSq_nonneg 2 _))
  have hM20 : 0 ≤ M2 := (hsSq_nonneg 2 (u 0)).trans (hM2 0 ⟨le_rfl, hTpos⟩)
  obtain ⟨A3, hA3⟩ := rpow_coeff_bound (K := K3) (m := m3) hM20
  obtain ⟨M3, hM3⟩ := hsSq_bounded_of_rate (s := 3) (A := A3) hν hm hT fun t ht =>
    (hK3 _ (hdata t ht)).trans (hA3 _ (hsSq_nonneg 2 _) (hM2 t ⟨ht.1.le, ht.2⟩) _
      (hsSq_nonneg 3 _))
  exact periodicHsBlowupAlternative hν.le (by norm_num) hν u₀ hu₀ u p hm T hT
    ⟨Real.sqrt M3, fun t ht => hsNorm_le_of_hsSq_le (hM3 t ht)⟩

/-- Coined. **Hypothesis (OPEN here; CF 1993 Biot–Savart stretching representation on `T³` with
the depletion factor `cfDepletion`, plus BdV–B 2002 interpolation; not formalized).** -/
def PeriodicHolderStretchingEstimate (ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure), IsPeriodicMaximalSolution ν u₀ u p →
      ∀ T : ℝ, periodicTstar ν u₀ = (T : EReal) → VortDirHolderHalf u T →
        ∃ K : ℝ, ∀ t ∈ Ioo (0:ℝ) T,
          rateOf 1 (fourierNSField ν (fourierCoeffVF (u t))) (fourierCoeffVF (u t)) ≤
            (K * h1Sq (u t)) * h1Sq (u t)

/-- Coined. **Hypothesis (OPEN here; classical consequence of the energy equality).** -/
def PeriodicEnstrophyTimeIntegrable (ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure), IsPeriodicMaximalSolution ν u₀ u p →
      ∀ T : ℝ, periodicTstar ν u₀ = (T : EReal) →
        ∃ G : ℝ → ℝ, ContinuousOn G (Icc 0 T) ∧ ∀ t ∈ Ioo (0:ℝ) T, HasDerivAt G (h1Sq (u t)) t

/-- **Proved.** The two analytic Props give `PeriodicDirectionEnstrophyGrowthL1`. -/
theorem periodicDirectionEnstrophyGrowthL1_of_holderStretching {ν : ℝ}
    (hS : PeriodicHolderStretchingEstimate ν) (hI : PeriodicEnstrophyTimeIntegrable ν) :
    PeriodicDirectionEnstrophyGrowthL1 ν := by
  intro hν u₀ hu₀ u p hm T hT hdir
  obtain ⟨K, hK⟩ := hS hν u₀ hu₀ u p hm T hT hdir
  obtain ⟨G, hGc, hGd⟩ := hI hν u₀ hu₀ u p hm T hT
  exact ⟨fun t => K * h1Sq (u t), fun t => K * G t, continuousOn_const.mul hGc,
    fun t ht => (hGd t ht).const_mul K, hK⟩

/-- **Proved (conditional).** `PeriodicBKMIntegrability` from the four classical Props and the
OPEN hidden property. -/
theorem periodicBKMIntegrability_of_classical_bending {ν : ℝ}
    (hS : PeriodicHolderStretchingEstimate ν) (hI : PeriodicEnstrophyTimeIntegrable ν)
    (h2 : PeriodicH2SmoothingRate ν) (h3 : PeriodicH3SmoothingRate ν)
    (hB : PeriodicBendingRateHiddenProperty ν) : PeriodicBKMIntegrability ν :=
  periodicBKMIntegrability_of_bending (periodicDirectionEnstrophyGrowthL1_of_holderStretching hS hI)
    (periodicH1BlowupCriterion_of_smoothing h2 h3) hB

end PeriodicNSContinuation
