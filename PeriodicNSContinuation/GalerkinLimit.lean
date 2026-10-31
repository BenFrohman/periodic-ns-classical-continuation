/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.FourierData

/-!
# Towards `PeriodicGalerkinLimit`

`PeriodicGalerkinLimit ν s` is split into three named sub-Props (all coined, all **NOT proved**):

* `GalerkinModeConvergence ν s` — compactness: a subsequence of the Galerkin solutions converges
  mode by mode at every time in `[0,T]`;
* `GalerkinLimitEquation ν s` — passage to the limit in the integrated Fourier NS equation;
* `FourierSolutionReconstruction ν s` — an `H^s` Fourier solution from smooth data gives a smooth
  periodic velocity and pressure.

**Proved:** the limit inherits the initial datum, Hermitian symmetry, `DivergenceFree`, and the
`H^s` bound (Fatou); and `periodicGalerkinLimit_of` derives `PeriodicGalerkinLimit ν s` from the
three sub-Props. Clay is not solved.
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D

namespace PeriodicNSContinuation

/-- Full (untruncated) Fourier NS vector field, matching `galerkinNSField` (coined). -/
def fourierNSField (ν : ℝ) (a : TorusFourierNS.FField) : TorusFourierNS.FField := fun k i =>
  -((TorusFourierNS.viscCoeff ν k : ℝ) : ℂ) * a k i -
    TorusFourierNS.lerayP k (fun j => 2 * Real.pi * Complex.I * ∑' m : TorusFourierNS.Mode,
      (∑ l, a m l * ((((k - m) l : ℤ)) : ℂ)) * a (k - m) j) i

/-- **NOT proved** (coined). Compactness on the Fourier side. -/
def GalerkinModeConvergence (ν s : ℝ) : Prop :=
  ∀ u₀ : NavierStokes3D.VelocityField, IsPeriodicSmoothInitialData u₀ → ∀ T : ℝ, 0 < T →
    ∀ (M : ℝ) (α : ∀ N : ℕ, ℝ → TorusFourierNS.GState N),
      (∀ N, IsGalerkinSolutionOn N ν (fourierCoeffVF u₀) T (α N)) →
      (∀ N, ∀ t ∈ Icc 0 T, TorusFourierNS.hsNormField s (TorusFourierNS.extendG (α N t)) ≤ M) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ a : ℝ → TorusFourierNS.FField, ∀ t ∈ Icc 0 T, ∀ k i,
        Tendsto (fun n => TorusFourierNS.extendG (α (φ n) t) k i) atTop (𝓝 (a t k i))

/-- **NOT proved** (coined). Passage to the limit in the integrated equation. -/
def GalerkinLimitEquation (ν s : ℝ) : Prop :=
  ∀ u₀ : NavierStokes3D.VelocityField, IsPeriodicSmoothInitialData u₀ → ∀ T : ℝ, 0 < T →
    ∀ (M : ℝ) (α : ∀ N : ℕ, ℝ → TorusFourierNS.GState N),
      (∀ N, IsGalerkinSolutionOn N ν (fourierCoeffVF u₀) T (α N)) →
      (∀ N, ∀ t ∈ Icc 0 T, TorusFourierNS.hsNormField s (TorusFourierNS.extendG (α N t)) ≤ M) →
      ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ a : ℝ → TorusFourierNS.FField,
      (∀ t ∈ Icc 0 T, ∀ k i,
        Tendsto (fun n => TorusFourierNS.extendG (α (φ n) t) k i) atTop (𝓝 (a t k i))) →
      ∀ t ∈ Icc 0 T, ∀ k i,
        a t k i = a 0 k i + ∫ τ in (0 : ℝ)..t, fourierNSField ν (a τ) k i

/-- **NOT proved** (coined). Regularity and reconstruction of a smooth solution and pressure. -/
def FourierSolutionReconstruction (ν s : ℝ) : Prop :=
  ∀ u₀ : NavierStokes3D.VelocityField, IsPeriodicSmoothInitialData u₀ → ∀ T : ℝ, 0 < T →
    ∀ (M : ℝ) (a : ℝ → TorusFourierNS.FField), a 0 = fourierCoeffVF u₀ →
      (∀ t ∈ Icc 0 T, TorusFourierNS.MemHsField s (a t) ∧
        TorusFourierNS.hsNormField s (a t) ≤ M ∧ TorusFourierNS.HermitianField (a t) ∧
        TorusFourierNS.DivergenceFree (a t)) →
      (∀ t ∈ Icc 0 T, ∀ k i,
        a t k i = a 0 k i + ∫ τ in (0 : ℝ)..t, fourierNSField ν (a τ) k i) →
      ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
        IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p

lemma eventually_mem_modeBox (k : TorusFourierNS.Mode) :
    ∀ᶠ N : ℕ in atTop, k ∈ TorusFourierNS.modeBox N := by
  refine eventually_atTop.2 ⟨∑ i, (k i).natAbs, fun N hN => ?_⟩
  simp only [TorusFourierNS.modeBox, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have h1 : (k i).natAbs ≤ N := le_trans (Finset.single_le_sum (f := fun i => (k i).natAbs)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) hN
  have h2 : ((k i).natAbs : ℤ) ≤ N := by exact_mod_cast h1
  constructor <;> cases abs_le.1 (Int.abs_eq_natAbs (k i) ▸ h2) <;> linarith

/-- **Proved.** The limit has the Fourier coefficients of the data at time `0`. -/
theorem limit_initial {ν T : ℝ} {a₀ : TorusFourierNS.FField}
    {α : ∀ N : ℕ, ℝ → TorusFourierNS.GState N} (hα : ∀ N, IsGalerkinSolutionOn N ν a₀ T (α N))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {a : TorusFourierNS.FField}
    (h : ∀ k i, Tendsto (fun n => TorusFourierNS.extendG (α (φ n) 0) k i) atTop (𝓝 (a k i))) :
    a = a₀ := by
  funext k i
  refine tendsto_nhds_unique (h k i) (tendsto_const_nhds.congr' ?_)
  filter_upwards [hφ.tendsto_atTop.eventually (eventually_mem_modeBox k)] with n hn
  rw [(hα (φ n)).1]
  simp [TorusFourierNS.extendG, TorusFourierNS.restrictG, hn]

/-- **Proved.** Hermitian symmetry passes to mode-wise limits. -/
theorem hermitian_of_tendsto {x : ℕ → TorusFourierNS.FField} {a : TorusFourierNS.FField}
    (hx : ∀ n, TorusFourierNS.HermitianField (x n))
    (h : ∀ k i, Tendsto (fun n => x n k i) atTop (𝓝 (a k i))) :
    TorusFourierNS.HermitianField a := fun k i =>
  tendsto_nhds_unique (h (-k) i) <| by
    have := (Complex.continuous_conj.tendsto _).comp (h k i)
    exact this.congr fun n => (hx n k i).symm

/-- **Proved.** `DivergenceFree` passes to mode-wise limits. -/
theorem divergenceFree_of_tendsto {x : ℕ → TorusFourierNS.FField} {a : TorusFourierNS.FField}
    (hx : ∀ n, TorusFourierNS.DivergenceFree (x n))
    (h : ∀ k i, Tendsto (fun n => x n k i) atTop (𝓝 (a k i))) :
    TorusFourierNS.DivergenceFree a := fun k => by
  have hl : Tendsto (fun n => TorusFourierNS.dot (TorusFourierNS.kvec k) (x n k)) atTop
      (𝓝 (TorusFourierNS.dot (TorusFourierNS.kvec k) (a k))) := by
    unfold TorusFourierNS.dot
    exact tendsto_finset_sum _ fun i _ => (h k i).const_mul _
  exact tendsto_nhds_unique hl (tendsto_const_nhds.congr fun n => (hx n k).symm)

lemma summable_hs_extendG (s : ℝ) {N : ℕ} (v : TorusFourierNS.GState N) :
    Summable fun p : TorusFourierNS.Mode × Fin 3 =>
      TorusFourierNS.sobW s p.1 * ‖TorusFourierNS.extendG v p.1 p.2‖ ^ 2 := by
  refine summable_of_ne_finset_zero (s := (TorusFourierNS.modeBox N) ×ˢ Finset.univ) ?_
  intro p hp
  have : p.1 ∉ TorusFourierNS.modeBox N := by
    intro h; exact hp (Finset.mem_product.2 ⟨h, Finset.mem_univ _⟩)
  simp [TorusFourierNS.extendG, this]

/-- **Proved (Fatou).** A uniform `H^s` bound passes to mode-wise limits of Galerkin states. -/
theorem hs_of_tendsto {s M : ℝ} {N : ℕ → ℕ} {x : ∀ n, TorusFourierNS.GState (N n)}
    {a : TorusFourierNS.FField}
    (hx : ∀ n, TorusFourierNS.hsNormField s (TorusFourierNS.extendG (x n)) ≤ M)
    (h : ∀ k i, Tendsto (fun n => TorusFourierNS.extendG (x n) k i) atTop (𝓝 (a k i))) :
    TorusFourierNS.MemHsField s a ∧ TorusFourierNS.hsNormField s a ≤ M := by
  have hM : 0 ≤ M := (Real.sqrt_nonneg _).trans (hx 0)
  have hw : ∀ p : TorusFourierNS.Mode × Fin 3, 0 ≤ TorusFourierNS.sobW s p.1 := fun p =>
    Real.rpow_nonneg (TorusFourierNS.one_add_sq_pos p.1).le _
  have hfin : ∀ F : Finset (TorusFourierNS.Mode × Fin 3),
      ∑ p ∈ F, TorusFourierNS.sobW s p.1 * ‖a p.1 p.2‖ ^ 2 ≤ M ^ 2 := by
    intro F
    have hl : Tendsto (fun n => ∑ p ∈ F, TorusFourierNS.sobW s p.1 *
        ‖TorusFourierNS.extendG (x n) p.1 p.2‖ ^ 2) atTop
        (𝓝 (∑ p ∈ F, TorusFourierNS.sobW s p.1 * ‖a p.1 p.2‖ ^ 2)) :=
      tendsto_finset_sum _ fun p _ => ((h p.1 p.2).norm.pow 2).const_mul _
    refine le_of_tendsto' hl fun n => ?_
    have hs := summable_hs_extendG s (x n)
    refine (hs.sum_le_tsum F fun p _ => mul_nonneg (hw p) (sq_nonneg _)).trans ?_
    have h0 : 0 ≤ ∑' p : TorusFourierNS.Mode × Fin 3, TorusFourierNS.sobW s p.1 *
        ‖TorusFourierNS.extendG (x n) p.1 p.2‖ ^ 2 :=
      tsum_nonneg fun p => mul_nonneg (hw p) (sq_nonneg _)
    have := hx n
    unfold TorusFourierNS.hsNormField at this
    rw [Real.sqrt_le_left hM] at this
    exact this
  have hsum : TorusFourierNS.MemHsField s a :=
    summable_of_sum_le (fun p => mul_nonneg (hw p) (sq_nonneg _)) hfin
  refine ⟨hsum, ?_⟩
  unfold TorusFourierNS.hsNormField
  rw [Real.sqrt_le_left hM]
  exact hsum.tsum_le_of_sum_le hfin

/-- **Proved.** `PeriodicGalerkinLimit ν s` from the three named sub-Props. -/
theorem periodicGalerkinLimit_of {ν s : ℝ} (hA : GalerkinModeConvergence ν s)
    (hC : GalerkinLimitEquation ν s) (hD : FourierSolutionReconstruction ν s) :
    PeriodicGalerkinLimit ν s := by
  intro u₀ hu₀ T hT ⟨M, hM⟩
  choose α hαs hαb using hM
  obtain ⟨φ, hφ, a, hconv⟩ := hA u₀ hu₀ T hT M α hαs hαb
  have hstr := galerkinStructurePreserved_of ν periodicDataDivFree u₀ hu₀
  have h0 : a 0 = fourierCoeffVF u₀ :=
    limit_initial hαs hφ (hconv 0 ⟨le_rfl, hT.le⟩)
  refine hD u₀ hu₀ T hT M a h0 (fun t ht => ?_) (hC u₀ hu₀ T hT M α hαs hαb φ hφ a hconv)
  have hHs := hs_of_tendsto (x := fun n => α (φ n) t) (fun n => hαb (φ n) t ht) (hconv t ht)
  exact ⟨hHs.1, hHs.2,
    hermitian_of_tendsto (fun n => (hstr (φ n) T (α (φ n)) (hαs (φ n)) t ht).1) (hconv t ht),
    divergenceFree_of_tendsto (fun n => (hstr (φ n) T (α (φ n)) (hαs (φ n)) t ht).2) (hconv t ht)⟩

/-- **Proved.** Arzelà–Ascoli-type diagonal extraction: a bounded, equi-Lipschitz (per
coordinate) sequence of maps `[0,T] → (ι → ℂ)`, `ι` countable, has a subsequence converging at
every time and every coordinate. -/
theorem exists_subseq_tendsto_of_equiLipschitz {T : ℝ} (hT : 0 < T) {ι : Type} [Countable ι] (x : ℕ → ℝ → ι → ℂ) (B : ι → ℝ)
    (hB : ∀ n, ∀ t ∈ Icc 0 T, ∀ j, ‖x n t j‖ ≤ B j) (L : ι → ℝ)
    (hL : ∀ n, ∀ t₁ ∈ Icc 0 T, ∀ t₂ ∈ Icc 0 T, ∀ j, ‖x n t₁ j - x n t₂ j‖ ≤ L j * |t₁ - t₂|) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ a : ℝ → ι → ℂ, ∀ t ∈ Icc 0 T, ∀ j,
      Tendsto (fun n => x (φ n) t j) atTop (𝓝 (a t j)) := by
  let D := {q : ℚ // (q : ℝ) ∈ Icc 0 T}
  obtain ⟨b, -, φ, hφ, hlim⟩ := (isCompact_univ_pi fun p : D × ι =>
    isCompact_closedBall (0 : ℂ) (B p.2)).tendsto_subseq (x := fun n (p : D × ι) => x n p.1 p.2)
    (fun n => mem_univ_pi.2 fun p => mem_closedBall_zero_iff.2 (hB n _ p.1.2 p.2))
  have hq : ∀ (q : D) j, Tendsto (fun n => x (φ n) q j) atTop (𝓝 (b (q, j))) := fun q j =>
    tendsto_pi_nhds.1 hlim (q, j)
  refine ⟨φ, hφ, fun t j => limUnder atTop (fun n => x (φ n) t j), fun t ht j => ?_⟩
  apply CauchySeq.tendsto_limUnder
  rw [Metric.cauchySeq_iff']
  intro ε hε
  set δ := ε / (3 * (|L j| + 1)) with hδ
  have hδp : 0 < δ := by positivity
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show max 0 (t - δ) < min T (t + δ) by
    rw [max_lt_iff, lt_min_iff, lt_min_iff]; refine ⟨⟨hT, ?_⟩, ?_, ?_⟩ <;> linarith [ht.1, ht.2])
  rw [max_lt_iff] at hr1; rw [lt_min_iff] at hr2
  let q : D := ⟨r, hr1.1.le, hr2.1.le⟩
  have htq : |t - r| < δ := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  have hLδ : |L j| * δ < ε / 3 := by
    rw [hδ, mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg (L j)]
  have hclose : ∀ n, dist (x (φ n) t j) (x (φ n) r j) < ε / 3 := fun n => by
    rw [dist_eq_norm]
    calc _ ≤ L j * |t - r| := hL _ t ht r q.2 j
      _ ≤ |L j| * |t - r| := mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _)
      _ ≤ |L j| * δ := mul_le_mul_of_nonneg_left htq.le (abs_nonneg _)
      _ < ε / 3 := hLδ
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 (hq q j).cauchySeq (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  calc dist (x (φ n) t j) (x (φ N) t j)
      ≤ dist (x (φ n) t j) (x (φ n) r j) + dist (x (φ n) r j) (x (φ N) r j) +
        dist (x (φ N) r j) (x (φ N) t j) := dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have := hclose N; rw [dist_comm] at this
        gcongr; exacts [hclose n, hN n hn]
    _ = ε := by ring

/-- **NOT proved** (coined). Mode-wise uniform Lipschitz bound in time for the Galerkin solutions
(from the ODE and the uniform `H^s` bound). -/
def GalerkinModeEquiLipschitz (ν s : ℝ) : Prop :=
  ∀ u₀ : NavierStokes3D.VelocityField, IsPeriodicSmoothInitialData u₀ → ∀ T : ℝ, 0 < T →
    ∀ (M : ℝ) (α : ∀ N : ℕ, ℝ → TorusFourierNS.GState N),
      (∀ N, IsGalerkinSolutionOn N ν (fourierCoeffVF u₀) T (α N)) →
      (∀ N, ∀ t ∈ Icc 0 T, TorusFourierNS.hsNormField s (TorusFourierNS.extendG (α N t)) ≤ M) →
      ∃ L : TorusFourierNS.Mode → ℝ, ∀ N, ∀ t₁ ∈ Icc 0 T, ∀ t₂ ∈ Icc 0 T, ∀ k i,
        ‖TorusFourierNS.extendG (α N t₁) k i - TorusFourierNS.extendG (α N t₂) k i‖ ≤
          L k * |t₁ - t₂|

/-- **Proved.** A single coefficient is controlled by the `H^s` norm. -/
theorem norm_extendG_le_of_hs {s M : ℝ} {N : ℕ} {v : TorusFourierNS.GState N}
    (hv : TorusFourierNS.hsNormField s (TorusFourierNS.extendG v) ≤ M)
    (k : TorusFourierNS.Mode) (i : Fin 3) :
    ‖TorusFourierNS.extendG v k i‖ ≤ Real.sqrt (M ^ 2 / TorusFourierNS.sobW s k) := by
  have hM : 0 ≤ M := (Real.sqrt_nonneg _).trans hv
  have hwpos : 0 < TorusFourierNS.sobW s k := Real.rpow_pos_of_pos (TorusFourierNS.one_add_sq_pos k) _
  have hterm := (summable_hs_extendG s v).le_tsum (k, i) fun p _ => mul_nonneg
    (Real.rpow_nonneg (TorusFourierNS.one_add_sq_pos p.1).le _) (sq_nonneg _)
  unfold TorusFourierNS.hsNormField at hv
  rw [Real.sqrt_le_left hM] at hv
  rw [← Real.sqrt_sq (norm_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  rw [le_div_iff₀ hwpos]
  linarith [hterm, hv]

/-- **Proved.** `GalerkinModeConvergence ν s` from `GalerkinModeEquiLipschitz ν s`. -/
theorem galerkinModeConvergence_of {ν s : ℝ} (hL : GalerkinModeEquiLipschitz ν s) :
    GalerkinModeConvergence ν s := by
  intro u₀ hu₀ T hT M α hαs hαb
  obtain ⟨L, hLip⟩ := hL u₀ hu₀ T hT M α hαs hαb
  obtain ⟨φ, hφ, a, ha⟩ := exists_subseq_tendsto_of_equiLipschitz hT
    (ι := TorusFourierNS.Mode × Fin 3)
    (fun n t p => TorusFourierNS.extendG (α n t) p.1 p.2)
    (fun p => Real.sqrt (M ^ 2 / TorusFourierNS.sobW s p.1))
    (fun n t ht p => norm_extendG_le_of_hs (hαb n t ht) p.1 p.2) (fun p => L p.1)
    (fun n t₁ h₁ t₂ h₂ p => hLip n t₁ h₁ t₂ h₂ p.1 p.2)
  exact ⟨φ, hφ, fun t k i => a t (k, i), fun t ht k i => ha t ht (k, i)⟩

/-- **Proved.** `PeriodicGalerkinLimit ν s` from `GalerkinModeEquiLipschitz`,
`GalerkinLimitEquation` and `FourierSolutionReconstruction`. -/
theorem periodicGalerkinLimit_of' {ν s : ℝ} (hL : GalerkinModeEquiLipschitz ν s)
    (hC : GalerkinLimitEquation ν s) (hD : FourierSolutionReconstruction ν s) :
    PeriodicGalerkinLimit ν s :=
  periodicGalerkinLimit_of (galerkinModeConvergence_of hL) hC hD

end PeriodicNSContinuation
