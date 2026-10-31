/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.SmallDataAttack
import PeriodicNSContinuation.CoeffODE

/-!
# Enstrophy identity on `T³` (Path 1, step 1)

* `periodicEnstrophyIdentity` — **proved, no hypotheses**. It is the `s = 1` case of the proved
  Fourier `H^s` energy identity: `t ↦ ‖u(t)‖²_{H¹}` is continuous on `[0,T']` and
  `d/dt ‖u‖²_{H¹} = rateOf 1 (fourierNSField ν û) û` on `(0,T')`.
* `riccati_barrier_Ioo` — **proved**: the Riccati barrier with derivatives only on the open
  interval, which is what the identity supplies.
* `periodicTstar_eq_top_of_smallH1_of_rate` — **proved** from the identity together with two named
  Props:
  - `PeriodicEnstrophyRateBound ν α β` (coined; the Ladyzhenskaya/Poincaré trilinear estimate,
    **not formalized**), required only for zero-mean data;
  - `PeriodicH1BlowupCriterion ν` (Leray, **not formalized**).

**Mean-mode caveat.** `h1Sq` is the inhomogeneous norm and includes `|û₀|²`, and the mean is
conserved. So the old `PeriodicEnstrophyRiccati ν α β` with `α > 0` would fail for a small
constant flow, where the derivative is `0` but `E(−α+βE²) < 0`. The new Prop is therefore
restricted to zero-mean data.
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D TorusFourierNS

namespace PeriodicNSContinuation

open Corrected

/-- **Proved, no hypotheses.** The `T³` enstrophy (`H¹`) energy identity. -/
theorem periodicEnstrophyIdentity (ν : ℝ) : PeriodicFourierHsEnergyIdentity ν 1 :=
  periodicFourierHsEnergyIdentity ν 1

/-- **Proved.** Riccati barrier with two-sided derivatives on `Ioo 0 T'` only. -/
theorem riccati_barrier_Ioo {f f' : ℝ → ℝ} {α β T' : ℝ} (hβ : 0 ≤ β)
    (hf : ContinuousOn f (Icc 0 T'))
    (hd : ∀ x ∈ Ioo 0 T', HasDerivAt f (f' x) x)
    (hle : ∀ x ∈ Ioo 0 T', f' x ≤ f x * (-α + β * f x ^ 2))
    (hnn : ∀ x, 0 ≤ f x) (hsmall : β * f 0 ^ 2 < α) :
    ∀ x ∈ Icc 0 T', f x ≤ f 0 := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with h0 | hxpos
  · rw [← h0]
  have hT' : 0 < T' := lt_of_lt_of_le hxpos hx.2
  have h0mem : (0:ℝ) ∈ Icc 0 T' := ⟨le_rfl, hT'.le⟩
  have htend : Tendsto f (𝓝[>] 0) (𝓝 (f 0)) := by
    have := (hf 0 h0mem).tendsto
    rw [← nhdsWithin_Ioo_eq_nhdsGT hT']
    exact this.mono_left (nhdsWithin_mono _ Ioo_subset_Icc_self)
  have hsm : ∀ᶠ a in 𝓝[>] (0:ℝ), β * f a ^ 2 < α := by
    have : Tendsto (fun a => β * f a ^ 2) (𝓝[>] 0) (𝓝 (β * f 0 ^ 2)) :=
      (htend.pow 2).const_mul β
    exact this.eventually (gt_mem_nhds hsmall)
  have hlt : ∀ᶠ a in 𝓝[>] (0:ℝ), a < x := by
    filter_upwards [Ioo_mem_nhdsGT hxpos] with a ha using ha.2
  have hpos : ∀ᶠ a in 𝓝[>] (0:ℝ), 0 < a := self_mem_nhdsWithin
  have key : ∀ᶠ a in 𝓝[>] (0:ℝ), f x ≤ f a := by
    filter_upwards [hsm, hlt, hpos] with a hsa hax ha0
    set g : ℝ → ℝ := fun y => f (a + y)
    have hg : ContinuousOn g (Icc 0 (x - a)) := by
      refine hf.comp (continuousOn_const.add continuousOn_id) fun y hy => ?_
      exact ⟨by linarith [hy.1], by linarith [hy.2, hx.2]⟩
    have hgd : ∀ y ∈ Ico 0 (x - a), HasDerivWithinAt g (f' (a + y)) (Ici y) y := by
      intro y hy
      have hm : a + y ∈ Ioo 0 T' := ⟨by linarith [hy.1], by linarith [hy.2, hx.2]⟩
      have := (hd _ hm).comp y ((hasDerivAt_id y).const_add a)
      simpa [g] using this.hasDerivWithinAt
    have hgle : ∀ y ∈ Ico 0 (x - a), f' (a + y) ≤ g y * (-α + β * g y ^ 2) := by
      intro y hy
      exact hle _ ⟨by linarith [hy.1], by linarith [hy.2, hx.2]⟩
    have := riccati_barrier hβ hg hgd hgle (hnn _) (by simpa [g] using hsa) (x - a)
      ⟨by linarith, le_rfl⟩
    simpa [g] using this
  exact ge_of_tendsto htend key

/-- Coined. **Hypothesis (classical, not formalized: Ladyzhenskaya `‖f‖_{L⁴} ≲ ‖f‖^{1/4}‖∇f‖^{3/4}`
together with Poincaré on zero-mean fields).** For zero-mean data, the `H¹` rate along the
solution is at most `E(−α + βE²)`. -/
def PeriodicEnstrophyRateBound (ν α β : ℝ) : Prop :=
  0 < ν → ∀ (u₀ : VelocityField) (u : TimeDependentVelocity) (p : TimeDependentPressure) (T' : ℝ),
    IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T' u p → (∀ i, fourierCoeffVF u₀ 0 i = 0) →
    ∀ t ∈ Ioo 0 T', rateOf 1 (fourierNSField ν (fourierCoeffVF (u t))) (fourierCoeffVF (u t)) ≤
      h1Sq (u t) * (-α + β * h1Sq (u t) ^ 2)

/-- **Proved** from the unconditional enstrophy identity, `PeriodicEnstrophyRateBound` and
`PeriodicH1BlowupCriterion`. Small zero-mean `H¹` data have infinite lifespan. -/
theorem periodicTstar_eq_top_of_smallH1_of_rate {ν α β : ℝ} (hν : 0 < ν) (hβ : 0 ≤ β)
    (hR : PeriodicEnstrophyRateBound ν α β) (hL : PeriodicH1BlowupCriterion ν)
    {u₀ : VelocityField} (hu₀ : IsPeriodicSmoothInitialData u₀)
    (hmean : ∀ i, fourierCoeffVF u₀ 0 i = 0)
    {u : TimeDependentVelocity} {p : TimeDependentPressure}
    (hm : IsPeriodicMaximalSolution ν u₀ u p) (hsmall : β * h1Sq u₀ ^ 2 < α) :
    periodicTstar ν u₀ = ⊤ := by
  rcases tstar_eq_top_or_coe hν hu₀ with h | ⟨T, hT⟩
  · exact h
  · exfalso
    apply hL hν u₀ hu₀ u p hm T hT
    refine ⟨h1Sq u₀, fun t ht => ?_⟩
    obtain ⟨hsol, htm, -⟩ := sol_around hm hT ht
    obtain ⟨hc, hd⟩ := periodicEnstrophyIdentity ν hν u₀ u p _ hsol
    have hu0 : u 0 = u₀ := u_zero hsol
    have := riccati_barrier_Ioo (f := fun t => h1Sq (u t)) hβ hc (fun x hx => (hd x hx).2)
      (hR hν u₀ u p _ hsol hmean) (fun _ => hsSq_nonneg 1 _) (by simpa [hu0] using hsmall) t htm
    simpa [hu0] using this

end PeriodicNSContinuation
