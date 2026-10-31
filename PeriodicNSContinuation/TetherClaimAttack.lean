/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.SmallDataAttack

/-!
# The tether claim and the direction criterion, tested against `PeriodicBKMIntegrability`

Work in progress. **Nothing here proves `PeriodicBKMIntegrability`.**

## Extracted claim (author's sources)
* Lean hypothesis `hDI` in `NS_Millennium_Proof/Modules/TetheredLyapunov.lean`
  (`global_regularity_of_constructions`) and `Modules/AnalyticPipeline.lean`: for each NS solution
  with data `u₀` there are `C, κ'' > 0` with `M' ≤ C M² − κ'' M³` for `M(t) = ‖ω(t)‖_∞`.
* The manuscript extract (`Frohmanian_Symplectic_Tether_NS_Proof.tex__key_extracts.txt`, line 1)
  says this "reduces … to a Riccati-type comparison ODE whose phase-plane analysis yields a
  uniform bound on ‖ω(t)‖_{L^∞}".
* `STATUS-2026-10-13.md` records that "derivation of the rate itself from the unmodified vorticity
  transport equation remains open".
Here the claim is `PeriodicTetherCubicRate ν` (coined). Its constants may depend on the data.

* `periodicVorticityAPrioriBound_of_tetherCubicRate` — **proved**: the claim gives the uniform
  bound `M ≤ max(M(0), C/κ'')`, hence `PeriodicBKMIntegrability` and Statement (B).
* `uniform_cubic_rate_false_of_scaling` — **proved (abstract scaling step)**: with constants
  *independent of the data*, the claim is incompatible with NS scaling. For `λ ∈ ℕ`,
  `u_λ = λ u(λx, λ²t)` is again a `ℤ³`-periodic solution, so `M' ≤ C M² − κ λ² M³` holds for all
  `λ`, which is impossible once `M > 0`. (The scaling covariance of solutions is not formalized.)
  Only the data-dependent version survives, and it is exactly as strong as global regularity.

## Direction of vorticity (Definition 7.1 of `artifacts/Frohman_What_Is_Actually_Proved_2026.tex`)
`VortDirHolderHalf` follows the author's wording: `|ξ(x,t) − ξ(y,t)| ≤ C|x−y|^{1/2}` where
`r(x,t), r(y,t) ≥ Ω`, for `t < T*`. The criterion (Beirão da Veiga–Berselli 2002, after
Constantin–Fefferman 1993) is the named hypothesis `PeriodicDirectionCriterion ν`.
`integrability_of_directionCriterion` is **proved** from it.

May/June sources mention Prodi–Serrin and Constantin–Fefferman only by name:
* `Blueprint.md`: "Extensions: Immediately yields Euler (ν=0), MHD, Prodi–Serrin etc.";
* `historical/docs/Context_of_evolution_Proof.txt:1981`: "Other Regularity Criteria (e.g.,
  Prodi–Serrin, …): The tether supplies the missing geometric control".
Neither gives a precise statement, so the classical formulations are used here.
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D

namespace PeriodicNSContinuation

open Corrected

/-- **Proved.** Cubic Riccati barrier: `f' ≤ C f² − κ f³`, `κ > 0`, `f(0) ≥ 0` give
`f ≤ max (f 0) (C/κ)`. -/
theorem cubic_riccati_barrier {f f' : ℝ → ℝ} {C κ T' : ℝ} (hκ : 0 < κ)
    (hf : ContinuousOn f (Icc 0 T'))
    (hd : ∀ x ∈ Ico 0 T', HasDerivWithinAt f (f' x) (Ici x) x)
    (hle : ∀ x ∈ Ico 0 T', f' x ≤ C * f x ^ 2 - κ * f x ^ 3) (h0 : 0 ≤ f 0) :
    ∀ x ∈ Icc 0 T', f x ≤ max (f 0) (C / κ) := by
  intro x hx
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have hB : f x ≤ max (f 0) (C / κ) + ε / 2 := by
    refine image_le_of_deriv_right_lt_deriv_boundary' (B := fun _ => max (f 0) (C / κ) + ε / 2)
      (B' := fun _ => 0) hf hd (by linarith [le_max_left (f 0) (C / κ)]) continuousOn_const
      (fun _ _ => hasDerivWithinAt_const _ _ _) ?_ hx
    intro y hy hyB
    have h1 := hle y hy
    rw [hyB] at h1
    set B := max (f 0) (C / κ) + ε / 2
    have hBpos : 0 < B := by have := le_max_left (f 0) (C / κ); simp only [B]; linarith
    have hκB : C < κ * B := by
      have : C / κ < B := by have := le_max_right (f 0) (C / κ); simp only [B]; linarith
      rwa [div_lt_iff₀ hκ, mul_comm] at this
    have : C * B ^ 2 - κ * B ^ 3 = B ^ 2 * (C - κ * B) := by ring
    nlinarith [mul_pos (pow_pos hBpos 2) (by linarith : (0:ℝ) < κ * B - C)]
  linarith

/-- Coined. **The extracted tether claim (OPEN for plain NS).** Data-dependent `C, κ'' > 0` with
`M' ≤ C M² − κ'' M³` (one-sided) for `M = ‖ω‖_∞` on every solution interval. -/
def PeriodicTetherCubicRate (ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∃ C κ : ℝ, 0 < κ ∧
      ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure) (T' : ℝ),
        IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T' u p →
        ∀ t ∈ Ico 0 T', ∃ d, HasDerivWithinAt (fun s => vorticity_sup_norm (vorticity (u s)))
          d (Ici t) t ∧
          d ≤ C * vorticity_sup_norm (vorticity (u t)) ^ 2 -
            κ * vorticity_sup_norm (vorticity (u t)) ^ 3

/-- **Proved.** The tether claim gives the κ = 0 a-priori bound. -/
theorem periodicVorticityAPrioriBound_of_tetherCubicRate {ν : ℝ}
    (h : PeriodicTetherCubicRate ν) : PeriodicVorticityAPrioriBound ν := by
  intro hν u₀ hu₀ u p hm T hT
  obtain ⟨C, κ, hκ, hrate⟩ := h hν u₀ hu₀
  refine ⟨max (vorticity_sup_norm (vorticity u₀)) (C / κ), fun t ht => ?_⟩
  obtain ⟨hsol, htm, -⟩ := sol_around hm hT ht
  have hc := (periodicSupNormContinuity ν hν u₀ u p _ hsol).2
  have hu0 : u 0 = u₀ := u_zero hsol
  choose! d hdd hdle using hrate u p _ hsol
  have := cubic_riccati_barrier hκ hc hdd hdle (vorticity_sup_norm_nonneg _) t htm
  simpa [hu0] using this

/-- **Proved (conditional).** Statement (B) from the extracted tether claim. -/
theorem clay_B_exact_of_tetherCubicRate (ν : ℝ) (h : PeriodicTetherCubicRate ν) :
    Clay_B_exact ν :=
  clay_B_exact_of_vorticityAPriori ν (periodicVorticityAPrioriBound_of_tetherCubicRate h)

/-- **Proved (abstract scaling step).** If at a point `M > 0` the rate held with `κ λ²` for every
`λ ≥ 1`, then we get a contradiction. NS scaling produces exactly this from a data-uniform rate. -/
theorem uniform_cubic_rate_false_of_scaling {d M C κ : ℝ} (hM : 0 < M) (hκ : 0 < κ)
    (h : ∀ lam : ℕ, 1 ≤ lam → d ≤ C * M ^ 2 - κ * (lam : ℝ) ^ 2 * M ^ 3) : False := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((|d| + |C| * M ^ 2 + 1) / (κ * M ^ 3))
  have hpos : 0 < κ * M ^ 3 := by positivity
  have h1 := h (n + 1) (by omega)
  have hn' : (|d| + |C| * M ^ 2 + 1) < (n : ℝ) * (κ * M ^ 3) := by rwa [div_lt_iff₀ hpos] at hn
  have hsq : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by push_cast; nlinarith
  have hC : C * M ^ 2 ≤ |C| * M ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  nlinarith [neg_abs_le d, mul_le_mul_of_nonneg_right hsq hpos.le]

/-! ## Direction of vorticity -/

/-- Coined, after Definition 7.1 of the author's note. The vorticity direction is `½`-Hölder on
the region where `|ω| ≥ Ω`, uniformly on `[0,T)`. -/
def VortDirHolderHalf (u : TimeDependentVelocity) (T : ℝ) : Prop :=
  ∃ Ω K : ℝ, 0 < Ω ∧ ∀ t ∈ Ico (0:ℝ) T, ∀ x y : T3,
    Ω ≤ ‖vorticity (u t) x‖ → Ω ≤ ‖vorticity (u t) y‖ →
      ‖‖vorticity (u t) x‖⁻¹ • vorticity (u t) x - ‖vorticity (u t) y‖⁻¹ • vorticity (u t) y‖ ≤
        K * Real.sqrt ‖x - y‖

/-- Coined. **Hypothesis (classical: Beirão da Veiga–Berselli 2002, after Constantin–Fefferman
1993; not formalized).** A finite lifespan rules out `½`-Hölder vorticity direction. -/
def PeriodicDirectionCriterion (ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure), IsPeriodicMaximalSolution ν u₀ u p →
      ∀ T : ℝ, periodicTstar ν u₀ = (T : EReal) → ¬ VortDirHolderHalf u T

/-- **Proved.** The direction criterion plus direction regularity up to any finite lifespan
gives integrability on every `[0,T]`. -/
theorem integrability_of_directionCriterion {ν : ℝ} (hν : 0 < ν)
    (hD : PeriodicDirectionCriterion ν) {u₀ : VelocityField}
    (hu₀ : IsPeriodicSmoothInitialData u₀) {u : TimeDependentVelocity}
    {p : TimeDependentPressure} (hm : IsPeriodicMaximalSolution ν u₀ u p)
    (hdir : ∀ T : ℝ, periodicTstar ν u₀ = (T : EReal) → VortDirHolderHalf u T) (T : ℝ) :
    IntegrableOn (fun t => vorticity_sup_norm (vorticity (u t))) (Icc 0 T) := by
  have htop : periodicTstar ν u₀ = ⊤ := by
    rcases tstar_eq_top_or_coe hν hu₀ with h | ⟨T', hT'⟩
    · exact h
    · exact absurd (hdir T' hT') (hD hν u₀ hu₀ u p hm T' hT')
  exact integrableOn_vorticity_of_lt_tstar hν hm (by rw [htop]; exact EReal.coe_lt_top T)

/-- Coined. **OPEN.** Every maximal solution has `½`-Hölder vorticity direction up to any finite
lifespan. -/
def PeriodicDirectionRegularity (ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure), IsPeriodicMaximalSolution ν u₀ u p →
      ∀ T : ℝ, periodicTstar ν u₀ = (T : EReal) → VortDirHolderHalf u T

/-- **Proved (conditional).** The criterion plus the open direction regularity give
`PeriodicBKMIntegrability`. -/
theorem periodicBKMIntegrability_of_direction {ν : ℝ} (hD : PeriodicDirectionCriterion ν)
    (hR : PeriodicDirectionRegularity ν) : PeriodicBKMIntegrability ν :=
  fun hν u₀ hu₀ u p hm T =>
    integrability_of_directionCriterion hν hD hu₀ hm (hR hν u₀ hu₀ u p hm) T

end PeriodicNSContinuation
