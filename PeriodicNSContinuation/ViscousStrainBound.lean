import Mathlib

/-!
# Viscous strain bound: what a `C(ν,t)` strain bound does and does not give

Abstract scalar layer for the surviving variant of the refuted `PeriodicStrainLinfBound`:
`‖S(t)‖_∞ ≤ c(t) ‖ω(t)‖_∞` for `t ∈ [t₀,T]`, with `c` allowed to depend on `ν` and `t`.
`M` stands for `‖ω(t)‖_∞`, `S` for `‖S(t)‖_∞`, `m` for the derivative of `M`.

* `ViscousStrainBound` and `VorticityMaxRiccati` are named hypothesis Props (see `NAMING.md`);
  neither is proved for Navier–Stokes here. `VorticityMaxRiccati` idealizes the classical
  `D⁺M ≤ ‖S‖_∞ M` (true as an upper Dini derivative; stated here with a derivative).
* Proved: `riccati_comparison` (`1/M + ∫c` is nondecreasing), `bound_of_viscousStrainBound`
  (`M(t) ≤ M₀/(1 - M₀∫c)` while `M₀∫c < 1`), and `riccati_saturates`: `M = 1/(1-t)` meets
  `M' = 1·M²` and is unbounded, so a strain bound with a bounded constant does not by itself
  prevent blow-up. The `C(ν,t)` route gives a lifespan / small-data statement, not regularity.
* `log_smoothing_split`: the arithmetic behind the log-corrected bound with `C^α` controlled
  by parabolic smoothing, `log(B (ντ)^{-α/2} R) = log B - (α/2) log(ντ) + log R`.
-/

open Set

namespace PeriodicNSContinuation.ViscousStrain

/-- Named hypothesis: strain controlled by vorticity with a time-dependent constant on `[t₀,T]`. -/
def ViscousStrainBound (M S c : ℝ → ℝ) (t₀ T : ℝ) : Prop :=
  ∀ t ∈ Icc t₀ T, S t ≤ c t * M t

/-- Named hypothesis: `M` is positive, differentiable with derivative `m`, and `m ≤ S·M`
(idealized vorticity-maximum inequality). -/
def VorticityMaxRiccati (M m S : ℝ → ℝ) (t₀ T : ℝ) : Prop :=
  ∀ t ∈ Icc t₀ T, 0 < M t ∧ HasDerivAt M (m t) t ∧ m t ≤ S t * M t

/-- `1/M + C` is monotone on `[t₀,T]` when `C' = c`. -/
theorem riccati_comparison {M m S c Cp : ℝ → ℝ} {t₀ T : ℝ}
    (hR : VorticityMaxRiccati M m S t₀ T) (hV : ViscousStrainBound M S c t₀ T)
    (hC : ∀ t ∈ Icc t₀ T, HasDerivAt Cp (c t) t) :
    MonotoneOn (fun t => 1 / M t + Cp t) (Icc t₀ T) := by
  have hd : ∀ t ∈ Icc t₀ T,
      HasDerivAt (fun t => 1 / M t + Cp t) (-(m t) / (M t)^2 + c t) t := by
    intro t ht
    obtain ⟨hM, hm, -⟩ := hR t ht
    have h1 := (hm.inv hM.ne').add (hC t ht)
    simp only [one_div]
    convert h1 using 1
  apply monotoneOn_of_deriv_nonneg (convex_Icc t₀ T)
  · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
  · exact fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht' := interior_subset ht
    rw [(hd t ht').deriv]
    obtain ⟨hM, -, hmS⟩ := hR t ht'
    have hS := hV t ht'
    have hM2 : 0 < (M t)^2 := by positivity
    have : m t ≤ c t * (M t)^2 := by nlinarith
    rw [neg_div, neg_add_eq_sub, sub_nonneg, div_le_iff₀ hM2]; linarith

/-- Lifespan-type consequence: while `M(t₀)·(C(t)-C(t₀)) < 1`, `M(t) ≤ M(t₀)/(1 - M(t₀)(C(t)-C(t₀)))`. -/
theorem bound_of_viscousStrainBound {M m S c Cp : ℝ → ℝ} {t₀ T : ℝ}
    (hR : VorticityMaxRiccati M m S t₀ T) (hV : ViscousStrainBound M S c t₀ T)
    (hC : ∀ t ∈ Icc t₀ T, HasDerivAt Cp (c t) t) {t : ℝ} (ht : t ∈ Icc t₀ T)
    (hsmall : M t₀ * (Cp t - Cp t₀) < 1) :
    M t ≤ M t₀ / (1 - M t₀ * (Cp t - Cp t₀)) := by
  have h0 : t₀ ∈ Icc t₀ T := ⟨le_rfl, ht.1.trans ht.2⟩
  have hmono := riccati_comparison hR hV hC h0 ht ht.1
  simp only at hmono
  have hM0 := (hR t₀ h0).1
  have hMt := (hR t ht).1
  have hden : 0 < 1 - M t₀ * (Cp t - Cp t₀) := by linarith
  rw [le_div_iff₀ hden]
  have key : 1 / M t₀ - (Cp t - Cp t₀) ≤ 1 / M t := by linarith
  have e1 : M t * (1 - M t₀ * (Cp t - Cp t₀)) = M t * M t₀ * (1 / M t₀ - (Cp t - Cp t₀)) := by
    field_simp
  rw [e1]
  calc M t * M t₀ * (1 / M t₀ - (Cp t - Cp t₀)) ≤ M t * M t₀ * (1 / M t) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = M t₀ := by field_simp

/-- A bounded strain constant does not prevent blow-up: `M(t) = 1/(1-t)` satisfies `M' = M²`. -/
theorem riccati_saturates {t : ℝ} (ht : t < 1) :
    HasDerivAt (fun s => 1 / (1 - s)) ((1 / (1 - t))^2) t := by
  have h : (1 - t) ≠ 0 := by linarith
  have := ((hasDerivAt_id t).const_sub 1).inv h
  simp only [one_div]
  convert this using 1
  simp [div_eq_mul_inv]

theorem riccati_saturates_unbounded :
    Filter.Tendsto (fun s : ℝ => 1 / (1 - s)) (nhdsWithin 1 (Iio 1)) Filter.atTop := by
  have h : Filter.Tendsto (fun s : ℝ => 1 - s) (nhdsWithin 1 (Iio 1)) (nhdsWithin 0 (Ioi 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have := ((continuous_const.sub continuous_id : Continuous (fun s : ℝ => (1:ℝ) - id s)).tendsto (1:ℝ)); simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs; simpa using hs
  simpa [one_div] using tendsto_inv_nhdsGT_zero.comp h

/-- Arithmetic of the smoothing-corrected logarithm. -/
theorem log_smoothing_split {B ν τ α R : ℝ} (hB : 0 < B) (hν : 0 < ν) (hτ : 0 < τ) (hR : 0 < R) :
    Real.log (B * (ν * τ) ^ (-(α / 2)) * R) = Real.log B - (α / 2) * Real.log (ν * τ) + Real.log R := by
  have hp : 0 < (ν * τ) ^ (-(α / 2)) := Real.rpow_pos_of_pos (by positivity) _
  rw [Real.log_mul (by positivity) hR.ne', Real.log_mul hB.ne' hp.ne', Real.log_rpow (by positivity)]
  ring

end PeriodicNSContinuation.ViscousStrain
