/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.BKMFinal

/-!
# Attacking `PeriodicBKMIntegrability` (work in progress; names coined unless noted)

`PeriodicBKMIntegrability ν` (FeffermanClayNS name) is the last open hypothesis of
`clay_B_exact_of_integrability`. This file does **not** prove it. It records what is proved:

* `integrableOn_vorticity_of_lt_tstar` — **proved**: below the lifespan, `∫₀ᵀ ‖ω‖_∞ < ∞`
  (the short-time case, from local existence and `periodicSupNormContinuity`).
* `periodicBKMIntegrability_iff_globalLifespan` — **proved**: `PeriodicBKMIntegrability ν` is
  *equivalent* to `PeriodicGlobalLifespan ν` (`T* = ⊤` for all smooth periodic data). So the open
  hypothesis is exactly global regularity. No weaker reformulation is hiding inside it.
* Route 2 (classical special cases, as named hypotheses):
  `integrability_of_smallDataGlobal` (small data), `integrability_of_prodiSerrin` (an endpoint
  Prodi–Serrin-type criterion plus a velocity bound).
* Route 1 (κ = 0 analogue of the tether): `periodicBKMIntegrability_of_vorticityAPriori` —
  **proved** from the sharpest named a-priori Prop `PeriodicVorticityAPrioriBound ν` (a uniform
  `‖ω‖_∞` bound up to any finite lifespan). Where it breaks: at κ = 0 there is no damping term.
  Enstrophy obeys only `E' ≤ C E³` (superlinear Riccati) and the max-point (Danskin) bound gives
  `Y' ≤ |∇u|_∞ Y ≲ Y² log(…)`. Neither yields a uniform bound, so the tether ceiling argument
  does not transfer. `PeriodicVorticityAPrioriBound` remains OPEN.
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D

namespace PeriodicNSContinuation

open Corrected

/-- Coined. **OPEN (equivalent to the Clay core).** Every smooth periodic datum has infinite
lifespan. -/
def PeriodicGlobalLifespan (ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ → periodicTstar ν u₀ = ⊤

/-- **Proved.** A degenerate interval carries no mass. -/
lemma integrableOn_Icc_of_nonpos {g : ℝ → ℝ} {T : ℝ} (hT : T ≤ 0) :
    IntegrableOn g (Icc 0 T) := by
  have h0 : (MeasureTheory.volume : Measure ℝ) (Icc (0:ℝ) T) = 0 := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_of_nonpos (by linarith)
  unfold IntegrableOn; rw [Measure.restrict_eq_zero.2 h0]; exact integrable_zero_measure

/-- **Proved (short-time / below-lifespan case).** If `T < T*`, then `∫₀ᵀ ‖ω(t)‖_∞ dt < ∞`. -/
theorem integrableOn_vorticity_of_lt_tstar {ν : ℝ} (hν : 0 < ν) {u₀ : VelocityField}
    {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (hm : IsPeriodicMaximalSolution ν u₀ u p) {T : ℝ} (hT : (T : EReal) < periodicTstar ν u₀) :
    IntegrableOn (fun t => vorticity_sup_norm (vorticity (u t))) (Icc 0 T) := by
  by_cases hT0 : 0 < T
  · exact ((periodicSupNormContinuity ν hν u₀ u p T (hm T hT0 hT)).2).integrableOn_Icc
  · exact integrableOn_Icc_of_nonpos (not_lt.1 hT0)

/-- **Proved.** Global lifespan gives `PeriodicBKMIntegrability`. -/
theorem periodicBKMIntegrability_of_globalLifespan {ν : ℝ} (h : PeriodicGlobalLifespan ν) :
    PeriodicBKMIntegrability ν := by
  intro hν u₀ hu₀ u p hm T
  exact integrableOn_vorticity_of_lt_tstar hν hm (by rw [h hν u₀ hu₀]; exact EReal.coe_lt_top T)

/-- **Proved.** `PeriodicBKMIntegrability` gives global lifespan (local existence, maximal
solution and BKM criterion are all proved). -/
theorem globalLifespan_of_periodicBKMIntegrability {ν : ℝ} (hint : PeriodicBKMIntegrability ν) :
    PeriodicGlobalLifespan ν := by
  intro hν u₀ hu₀
  obtain ⟨u, p, hm⟩ := periodicMaximalSolution_of_uniqueness
    (periodicVelocityUniqueness_of_energy ν (periodicEnergyDifferenceEstimate hν.le)) hν u₀ hu₀
  exact periodicTstar_eq_top_of_bkm ν hν (periodicLocalExistence_of_nonneg hν.le)
    (periodicBKMCriterion ν) hint u₀ hu₀ u p hm

/-- **Proved.** The open hypothesis is exactly global regularity of the lifespan. -/
theorem periodicBKMIntegrability_iff_globalLifespan (ν : ℝ) :
    PeriodicBKMIntegrability ν ↔ PeriodicGlobalLifespan ν :=
  ⟨globalLifespan_of_periodicBKMIntegrability, periodicBKMIntegrability_of_globalLifespan⟩

/-- **Proved (conditional).** Statement (B) from `PeriodicGlobalLifespan`. -/
theorem clay_B_exact_of_globalLifespan (ν : ℝ) (h : PeriodicGlobalLifespan ν) : Clay_B_exact ν :=
  clay_B_exact_of_integrability ν (periodicBKMIntegrability_of_globalLifespan h)

/-- **Proved.** A finite lifespan is a real number (local existence rules out `⊥`). -/
lemma tstar_eq_top_or_coe {ν : ℝ} (hν : 0 < ν) {u₀ : VelocityField}
    (hu₀ : IsPeriodicSmoothInitialData u₀) :
    periodicTstar ν u₀ = ⊤ ∨ ∃ T : ℝ, periodicTstar ν u₀ = (T : EReal) := by
  by_cases htop : periodicTstar ν u₀ = ⊤
  · exact Or.inl htop
  · have hbot : periodicTstar ν u₀ ≠ ⊥ :=
      ne_bot_of_gt (periodicLocalExistence_of_nonneg hν.le hν u₀ hu₀)
    exact Or.inr ⟨_, (EReal.coe_toReal htop hbot).symm⟩

/-! ## Route 2: classical special cases as named hypotheses -/

/-- Coined. **Hypothesis (classical for suitable `N`, e.g. Fujita–Kato `Ḣ^{1/2}` smallness; not
formalized).** Data with `N u₀ < ε` have infinite lifespan. -/
def PeriodicSmallDataGlobal (ν : ℝ) (N : VelocityField → ℝ) (ε : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ → N u₀ < ε →
    periodicTstar ν u₀ = ⊤

/-- **Proved.** Small-data integrability for every `T`. -/
theorem integrability_of_smallDataGlobal {ν ε : ℝ} {N : VelocityField → ℝ} (hν : 0 < ν)
    (h : PeriodicSmallDataGlobal ν N ε) {u₀ : VelocityField} (hu₀ : IsPeriodicSmoothInitialData u₀)
    (hN : N u₀ < ε) {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (hm : IsPeriodicMaximalSolution ν u₀ u p) (T : ℝ) :
    IntegrableOn (fun t => vorticity_sup_norm (vorticity (u t))) (Icc 0 T) :=
  integrableOn_vorticity_of_lt_tstar hν hm (by rw [h hν u₀ hu₀ hN]; exact EReal.coe_lt_top T)

/-- Coined. `‖v‖_∞ = ⨆ x, ‖v x‖`. -/
def velSupNorm (v : VelocityField) : ℝ := ⨆ x, ‖v x‖

/-- Coined. **Hypothesis (classical: Prodi 1959, Serrin 1962, endpoint `L^∞_t L^∞_x`; not
formalized).** A finite lifespan forces the velocity sup norm to be unbounded. -/
def PeriodicProdiSerrinCriterion (ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure), IsPeriodicMaximalSolution ν u₀ u p →
      ∀ T : ℝ, periodicTstar ν u₀ = (T : EReal) →
        ¬ ∃ M : ℝ, ∀ t ∈ Ico (0:ℝ) T, velSupNorm (u t) ≤ M

/-- **Proved.** Prodi–Serrin criterion plus a velocity bound up to any finite lifespan gives
integrability on every `[0,T]`. -/
theorem integrability_of_prodiSerrin {ν : ℝ} (hν : 0 < ν) (hPS : PeriodicProdiSerrinCriterion ν)
    {u₀ : VelocityField} (hu₀ : IsPeriodicSmoothInitialData u₀) {u : TimeDependentVelocity}
    {p : TimeDependentPressure} (hm : IsPeriodicMaximalSolution ν u₀ u p)
    (hb : ∀ T : ℝ, periodicTstar ν u₀ = (T : EReal) →
      ∃ M : ℝ, ∀ t ∈ Ico (0:ℝ) T, velSupNorm (u t) ≤ M) (T : ℝ) :
    IntegrableOn (fun t => vorticity_sup_norm (vorticity (u t))) (Icc 0 T) := by
  have htop : periodicTstar ν u₀ = ⊤ := by
    rcases tstar_eq_top_or_coe hν hu₀ with h | ⟨T', hT'⟩
    · exact h
    · exact absurd (hb T' hT') (hPS hν u₀ hu₀ u p hm T' hT')
  exact integrableOn_vorticity_of_lt_tstar hν hm (by rw [htop]; exact EReal.coe_lt_top T)

/-! ## Route 1: κ = 0 analogue of the tether ceiling -/

/-- Coined. **OPEN (the sharp κ = 0 a-priori estimate).** Up to any finite lifespan,
`‖ω(t)‖_∞` stays bounded. -/
def PeriodicVorticityAPrioriBound (ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure), IsPeriodicMaximalSolution ν u₀ u p →
      ∀ T : ℝ, periodicTstar ν u₀ = (T : EReal) →
        ∃ M : ℝ, ∀ t ∈ Ico (0:ℝ) T, vorticity_sup_norm (vorticity (u t)) ≤ M

/-- **Proved.** Continuity on `[0,T*)` of `t ↦ ‖ω(t)‖_∞` for a maximal solution. -/
lemma continuousOn_vorticity_Ico {ν : ℝ} (hν : 0 < ν) {u₀ : VelocityField}
    {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (hm : IsPeriodicMaximalSolution ν u₀ u p) {T : ℝ} (hT : periodicTstar ν u₀ = (T : EReal)) :
    ContinuousOn (fun t => vorticity_sup_norm (vorticity (u t))) (Ico 0 T) := by
  intro t ht
  obtain ⟨hsol, htm, -⟩ := sol_around hm hT ht
  have hc := (periodicSupNormContinuity ν hν u₀ u p _ hsol).2 t htm
  refine hc.mono_of_mem_nhdsWithin ?_
  refine mem_nhdsWithin.2 ⟨Iio ((t + T) / 2), isOpen_Iio, by simp; linarith [ht.2], ?_⟩
  rintro y ⟨hy1, hy2⟩
  exact ⟨hy2.1, le_of_lt hy1⟩

/-- **Proved.** Bounded and continuous on `[0,T)` gives integrable on `[0,T]`. -/
lemma integrableOn_Icc_of_bdd_Ico {g : ℝ → ℝ} {T M : ℝ} (hc : ContinuousOn g (Ico 0 T))
    (hb : ∀ t ∈ Ico (0:ℝ) T, ‖g t‖ ≤ M) : IntegrableOn g (Icc 0 T) := by
  apply (integrableOn_Icc_iff_integrableOn_Ico enorm_ne_top).2
  refine ⟨hc.aestronglyMeasurable measurableSet_Ico, ?_⟩
  exact HasFiniteIntegral.restrict_of_bounded (C := M) (by simp [Real.volume_Ico])
    (ae_restrict_of_forall_mem measurableSet_Ico hb)

/-- **Proved (Route 1 reduction).** The κ = 0 a-priori bound gives `PeriodicBKMIntegrability`. -/
theorem periodicBKMIntegrability_of_vorticityAPriori {ν : ℝ}
    (h : PeriodicVorticityAPrioriBound ν) : PeriodicBKMIntegrability ν := by
  intro hν u₀ hu₀ u p hm T
  have htop : periodicTstar ν u₀ = ⊤ := by
    rcases tstar_eq_top_or_coe hν hu₀ with h' | ⟨T', hT'⟩
    · exact h'
    · exfalso
      obtain ⟨M, hM⟩ := h hν u₀ hu₀ u p hm T' hT'
      apply periodicBKMCriterion ν hν u₀ hu₀ u p hm T' hT'
      refine integrableOn_Icc_of_bdd_Ico (M := M) (continuousOn_vorticity_Ico hν hm hT') ?_
      intro t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (vorticity_sup_norm_nonneg _)]
      exact hM t ht
  exact integrableOn_vorticity_of_lt_tstar hν hm (by rw [htop]; exact EReal.coe_lt_top T)

/-- **Proved (conditional).** Statement (B) from the open κ = 0 a-priori bound. -/
theorem clay_B_exact_of_vorticityAPriori (ν : ℝ) (h : PeriodicVorticityAPrioriBound ν) :
    Clay_B_exact ν :=
  clay_B_exact_of_integrability ν (periodicBKMIntegrability_of_vorticityAPriori h)

end PeriodicNSContinuation
