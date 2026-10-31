/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.BKMGronwall

/-!
# BKM pieces (names coined)

1. `periodicSupNormContinuity` — **proved**: `PeriodicSupNormContinuity ν` for every `ν`.
2. `PeriodicTameHsBound s`, `PeriodicLogSobolevBKMBound s` — the tame and log hypotheses with
   existential constants depending only on `s`; `periodicBKMHsControl_of_bounds` and
   `clay_B_exact_of_bounds` take no free constants.
3. Brezis–Gallouet, Fourier side (start): `fourier_split_bound` (split at `|k| ≤ R`, Cauchy–Schwarz
   on the tail), `tailWeight_tendsto_zero`, `fourier_split_eps`. **Proved.**
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D TorusFourierNS
open scoped ContDiff

namespace PeriodicNSContinuation

open Corrected Torus Clamp

/-! ### 1. Continuity of sup norms -/

/-- Coined. **Proved.** Sup norm in `x` of a field continuous on `[0,T] × ℝ³` and periodic in `x`
is continuous in `t`. -/
theorem supNorm_continuousOn {E : Type*} [NormedAddCommGroup E] {T : ℝ} (hT : 0 ≤ T)
    {F : ℝ → T3 → E} (hF : ContinuousOn (fun q : ℝ × T3 => F q.1 q.2) (S T))
    (hper : ∀ t ∈ Icc (0:ℝ) T, IsZ3Periodic (F t)) :
    ContinuousOn (fun t => ⨆ x, ‖F t x‖) (Icc 0 T) := by
  set K : Set T3 := (fun r : ℝ × ℝ × ℝ => toT3 r.1 r.2.1 r.2.2) ''
    (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
  have hK : IsCompact K := (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).image
    continuous_toT3'
  set G : ℝ → T3 → ℝ := fun t x => ‖F (cl T t) x‖
  have hG : Continuous ↿G := by
    have : Continuous fun q : ℝ × T3 => F (cl T q.1) q.2 :=
      hF.comp_continuous (((continuous_cl T).comp continuous_fst).prodMk continuous_snd)
        fun q => ⟨cl_mem hT _, trivial⟩
    exact this.norm
  refine (hK.continuous_sSup hG).continuousOn.congr fun t ht => ?_
  simp only [G, cl_of_mem ht, iSup]
  congr 1
  ext r; constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, ha, b, hb, c, hc, k, rfl⟩ := exists_cell x
    exact ⟨toT3 a b c, ⟨(a, b, c), ⟨ha, hb, hc⟩, rfl⟩, by show ‖F t _‖ = ‖F t _‖; rw [hper t ht]⟩
  · rintro ⟨x, -, rfl⟩; exact ⟨x, rfl⟩

local notation "e" k => EuclideanSpace.single k (1 : ℝ)

/-- Coined. The curl as a function of the derivative. -/
def curlOf (L : T3 →L[ℝ] T3) : T3 :=
  EuclideanSpace.single 0 (L (e 1) 2 - L (e 2) 1) +
    EuclideanSpace.single 1 (L (e 2) 0 - L (e 0) 2) +
    EuclideanSpace.single 2 (L (e 0) 1 - L (e 1) 0)

lemma continuous_single' (i : Fin 3) :
    Continuous (fun r : ℝ => (EuclideanSpace.single i r : T3)) := by
  have : (fun r : ℝ => (EuclideanSpace.single i r : T3)) = fun r : ℝ => r • (e i) := by
    funext r; ext j; simp
  rw [this]; fun_prop

lemma continuous_curlOf : Continuous curlOf := by
  unfold curlOf
  refine (((continuous_single' 0).comp ?_).add ((continuous_single' 1).comp ?_)).add
    ((continuous_single' 2).comp ?_) <;> fun_prop

lemma directionalCoord_eq {v : VelocityField} {x : T3} (hv : DifferentiableAt ℝ v x)
    (c d : Fin 3) : directionalCoord v c d x = fderiv ℝ v x (e d) c := by
  unfold directionalCoord
  have : (fun y => v y c) = (EuclideanSpace.proj c : T3 →L[ℝ] ℝ) ∘ v := rfl
  rw [this, ((EuclideanSpace.proj c).hasFDerivAt.comp x hv.hasFDerivAt).fderiv]
  rfl

lemma curl_eq_curlOf {v : VelocityField} (hv : Differentiable ℝ v) (x : T3) :
    curl v x = curlOf (fderiv ℝ v x) := by
  unfold curl curlOf; simp only [directionalCoord_eq (hv x)]

/-- **Proved** (for every `ν`). -/
theorem periodicSupNormContinuity (ν : ℝ) : PeriodicSupNormContinuity ν := by
  intro _ u₀ u p T' hsol
  have hT := hsol.1
  have hu := hsol.2.2.2.1
  have hD : ContinuousOn (fun q : ℝ × T3 => fderiv ℝ (u q.1) q.2) (S T') := by
    refine ((continuousOn_D hu hT).clm_comp
      (continuousOn_const (c := ContinuousLinearMap.inr ℝ ℝ T3))).congr fun q hq => ?_
    exact fderiv_slice hu hq.1 q.2
  have hdiff : ∀ t ∈ Icc (0:ℝ) T', Differentiable ℝ (u t) := fun t ht =>
    (contDiff_slice hu ht).differentiable (by simp)
  refine ⟨supNorm_continuousOn hT.le hD fun t ht => isZ3Periodic_fderiv (hsol.2.1 t ht), ?_⟩
  have hC : ContinuousOn (fun q : ℝ × T3 => vorticity (u q.1) q.2) (S T') :=
    (continuous_curlOf.comp_continuousOn hD).congr fun q hq =>
      curl_eq_curlOf (hdiff q.1 hq.1) q.2
  refine supNorm_continuousOn (F := fun t => vorticity (u t)) hT.le hC fun t ht x k => ?_
  show curl (u t) _ = curl (u t) x
  rw [curl_eq_curlOf (hdiff t ht), curl_eq_curlOf (hdiff t ht),
    isZ3Periodic_fderiv (hsol.2.1 t ht)]

/-! ### 2. Existential constants -/

/-- Coined. **Hypothesis (Kato–Ponce):** one `C ≥ 0`, depending only on `s`, for all `ν`. -/
def PeriodicTameHsBound (s : ℝ) : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ ν, PeriodicTameHsInequality ν s C

/-- Coined. **Hypothesis (Brezis–Gallouet / BKM):** one `K ≥ 0`, depending only on `s`. -/
def PeriodicLogSobolevBKMBound (s : ℝ) : Prop := ∃ K : ℝ, 0 ≤ K ∧ PeriodicLogSobolevBKM s K

/-- **Proved** from the two hypotheses (continuity is now proved). -/
theorem periodicGradHsControl_of_bound {s : ℝ} (ν : ℝ) (h : PeriodicTameHsBound s) :
    PeriodicGradHsControl ν s :=
  let ⟨_, hC, hc⟩ := h; periodicGradHsControl hC (hc ν) (periodicSupNormContinuity ν)

/-- **Proved** from the two hypotheses. -/
theorem periodicBKMHsControl_of_bounds {s : ℝ} (ν : ℝ) (htame : PeriodicTameHsBound s)
    (hlog : PeriodicLogSobolevBKMBound s) : PeriodicBKMHsControl ν s :=
  let ⟨_, hC, hc⟩ := htame; let ⟨_, hK, hk⟩ := hlog
  periodicBKMHsControl_of_tame_log hC hK (hc ν) (periodicSupNormContinuity ν) hk

/-- **Conditional.** `Clay_B_exact ν` from the two hypotheses and the OPEN
`PeriodicBKMIntegrability ν`. Clay is not solved. -/
theorem clay_B_exact_of_bounds {s : ℝ} (ν : ℝ) (hs : 5 / 2 < s) (htame : PeriodicTameHsBound s)
    (hlog : PeriodicLogSobolevBKMBound s) (hint : PeriodicBKMIntegrability ν) : Clay_B_exact ν :=
  clay_B_exact_of_hsControl ν s hs (periodicBKMHsControl_of_bounds ν htame hlog) hint

/-! ### 3. Brezis–Gallouet, Fourier side -/

/-- Coined. `|k|²`. -/
def modeSq (k : Mode) : ℝ := ∑ i, ((k i : ℝ)) ^ 2

/-- Coined. Tail weight `∑_{|k| > R} (1+|k|²)^{-s}`. -/
def tailWeight (s R : ℝ) : ℝ := ∑' k : Mode, if modeSq k ≤ R ^ 2 then 0 else sobW (-s) k

lemma cs_tsum {f g : Mode → ℝ} (hf : ∀ k, 0 ≤ f k) (hg : ∀ k, 0 ≤ g k)
    (hf2 : Summable fun k => f k ^ 2) (hg2 : Summable fun k => g k ^ 2) :
    Summable (fun k => f k * g k) ∧
      ∑' k, f k * g k ≤ Real.sqrt (∑' k, f k ^ 2) * Real.sqrt (∑' k, g k ^ 2) := by
  have h := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two hf hg
    (by simpa [Real.rpow_two] using hf2) (by simpa [Real.rpow_two] using hg2)
  refine ⟨h.1, ?_⟩
  have := h.2
  simp only [Real.rpow_two] at this
  rwa [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

/-- **Proved.** Low/high split at radius `R` with Cauchy–Schwarz on the high part:
`∑|c_k| ≤ ∑_{|k|≤R} |c_k| + (tailWeight s R)^{1/2} ‖c‖_{H^s}`. -/
theorem fourier_split_bound {s : ℝ} (hs : 3 / 2 < s) (c : Mode → ℝ)
    (hc : Summable fun k => sobW s k * c k ^ 2) (R : ℝ) :
    Summable (fun k => |c k|) ∧
    ∑' k, |c k| ≤ ∑' k, (if modeSq k ≤ R ^ 2 then |c k| else 0) +
      Real.sqrt (tailWeight s R) * Real.sqrt (∑' k, sobW s k * c k ^ 2) := by
  set g := fun k => Real.sqrt (sobW s k) * |c k|
  have hg0 : ∀ k, 0 ≤ g k := fun k => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  have hg2 : ∀ k, g k ^ 2 = sobW s k * c k ^ 2 := fun k => by
    simp only [g, mul_pow, Real.sq_sqrt (sobW_pos s k).le, sq_abs]
  have hgs : Summable fun k => g k ^ 2 := by simpa [hg2] using hc
  set f := fun k : Mode => if modeSq k ≤ R ^ 2 then 0 else Real.sqrt (sobW (-s) k)
  have hf0 : ∀ k, 0 ≤ f k := fun k => by simp only [f]; split_ifs <;> simp [Real.sqrt_nonneg]
  have hf2 : ∀ k, f k ^ 2 = if modeSq k ≤ R ^ 2 then 0 else sobW (-s) k := fun k => by
    simp only [f]; split_ifs <;> simp [Real.sq_sqrt (sobW_pos _ k).le]
  have hW := summable_sobW_neg hs
  have hfs : Summable fun k => f k ^ 2 := by
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) hW
    rw [hf2]; split_ifs <;> simp [(sobW_pos _ k).le]
  set F := fun k : Mode => Real.sqrt (sobW (-s) k)
  have hFs : Summable fun k => F k ^ 2 := by simpa [F, Real.sq_sqrt (sobW_pos _ _).le] using hW
  have hcF : ∀ k, |c k| = F k * g k := fun k => by
    simp only [F, g, ← mul_assoc, sqrt_sobW_neg_mul, one_mul]
  have habs : Summable fun k => |c k| := by
    simpa [hcF] using (cs_tsum (fun k => Real.sqrt_nonneg _) hg0 hFs hgs).1
  have hsplit : ∀ k, |c k| = (if modeSq k ≤ R ^ 2 then |c k| else 0) + f k * g k := fun k => by
    simp only [f]; split_ifs <;> simp [hcF, F]
  have hlow : Summable fun k => if modeSq k ≤ R ^ 2 then |c k| else 0 :=
    Summable.of_nonneg_of_le (fun k => by split_ifs <;> simp) (fun k => by split_ifs <;> simp) habs
  obtain ⟨hfg, hcs⟩ := cs_tsum hf0 hg0 hfs hgs
  refine ⟨habs, ?_⟩
  rw [tsum_congr hsplit, hlow.tsum_add hfg]
  have e1 : ∑' k, f k ^ 2 = tailWeight s R := by simp only [hf2, tailWeight]
  have e2 : ∑' k, g k ^ 2 = ∑' k, sobW s k * c k ^ 2 := by simp only [hg2]
  rw [e1, e2] at hcs
  linarith

/-- **Proved.** The tail weight tends to `0` as `R → ∞` (`s > 3/2`). -/
theorem tailWeight_tendsto_zero {s : ℝ} (hs : 3 / 2 < s) :
    Tendsto (tailWeight s) atTop (𝓝 0) := by
  have := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (g := fun _ : Mode => (0:ℝ))
    (f := fun R k => if modeSq k ≤ R ^ 2 then 0 else sobW (-s) k) (summable_sobW_neg hs)
    (fun k => by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (Real.sqrt (modeSq k))] with R hR
      have h0 : 0 ≤ modeSq k := Finset.sum_nonneg fun i _ => sq_nonneg _
      have : modeSq k ≤ R ^ 2 := by
        have := Real.sq_sqrt h0
        nlinarith [Real.sqrt_nonneg (modeSq k)]
      simp [this])
    (Eventually.of_forall fun R k => by
      by_cases h : modeSq k ≤ R ^ 2 <;> simp [h, abs_of_pos (sobW_pos _ k), (sobW_pos _ k).le])
  simpa [tailWeight] using this

/-- **Proved.** For every `ε > 0` there is `R` with
`∑|c_k| ≤ ∑_{|k|≤R} |c_k| + ε ‖c‖_{H^s}` for all `c` (with `‖c‖_{H^s}² = ∑ w_k c_k²`). -/
theorem fourier_split_eps {s : ℝ} (hs : 3 / 2 < s) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ c : Mode → ℝ, Summable (fun k => sobW s k * c k ^ 2) →
      ∑' k, |c k| ≤ ∑' k, (if modeSq k ≤ R ^ 2 then |c k| else 0) +
        ε * Real.sqrt (∑' k, sobW s k * c k ^ 2) := by
  obtain ⟨R, hR⟩ := ((tailWeight_tendsto_zero hs).eventually (gt_mem_nhds (by positivity :
    (0:ℝ) < ε ^ 2))).exists
  refine ⟨R, fun c hc => (fourier_split_bound hs c hc R).2.trans ?_⟩
  have hsq : Real.sqrt (tailWeight s R) ≤ ε := by
    rw [show ε = Real.sqrt (ε ^ 2) from (Real.sqrt_sq hε.le).symm]
    exact Real.sqrt_le_sqrt hR.le
  gcongr

end PeriodicNSContinuation
