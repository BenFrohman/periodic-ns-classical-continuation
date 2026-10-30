/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.Uniqueness
import PeriodicNSContinuation.TorusField
import PeriodicNSContinuation.FieldIdentities
import PeriodicNSContinuation.Clamp

/-!
# Proof of `PeriodicEnergyDifferenceEstimate` (for `ν ≥ 0`)

For two solutions `u, v` on `[0, T]` from the same data, with `w = u − v`,
`E(t) = ∫_{[0,1]³} |w(t)|²` satisfies `E' ≤ 2C E`, where `C` bounds `‖∇v‖` on
`[0, T] × [0,1]³`. The three terms `⟨w, (u·∇)w⟩`, `⟨w, Δw⟩` and `⟨w, ∇(p − q)⟩` are put in
divergence form (`FieldIdentities.lean`) and integrate to `0`, `≤ 0` and `0` over the unit cell
(`TorusField.lean`). The time derivative of `E` is taken after extending the integrand past
`[0, T]` by tangent lines (`Clamp.lean`).
-/

open FeffermanClayNS NavierStokes3D Set Filter Topology InnerProductSpace
open WeightedEnstrophy.Torus PeriodicNSContinuation.Torus PeriodicNSContinuation.Fields
open PeriodicNSContinuation.Clamp
open scoped RealInnerProductSpace ContDiff

namespace PeriodicNSContinuation.Corrected

local notation "e" k => EuclideanSpace.single k (1 : ℝ)

section regularity

variable {T : ℝ} {u : TimeDependentVelocity}

/-- The space-time set `[0, T] × ℝ³`. -/
abbrev S (T : ℝ) : Set (ℝ × T3) := Icc (0 : ℝ) T ×ˢ univ

lemma uniqueDiffOn_S (hT : 0 < T) : UniqueDiffOn ℝ (S T) :=
  (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ

/-- Joint derivative on `[0, T] × ℝ³`. -/
noncomputable def D (T : ℝ) (u : TimeDependentVelocity) (q : ℝ × T3) : ℝ × T3 →L[ℝ] T3 :=
  fderivWithin ℝ (fun q : ℝ × T3 => u q.1 q.2) (S T) q

variable (hu : ContDiffOn ℝ ∞ (fun q : ℝ × T3 => u q.1 q.2) (S T))
include hu

lemma continuousOn_D (hT : 0 < T) : ContinuousOn (D T u) (S T) :=
  hu.continuousOn_fderivWithin (uniqueDiffOn_S hT) (by simp)

lemma hasFDerivWithinAt_D {q : ℝ × T3} (hq : q ∈ S T) :
    HasFDerivWithinAt (fun q : ℝ × T3 => u q.1 q.2) (D T u q) (S T) q :=
  ((hu.differentiableOn (by simp)) q hq).hasFDerivWithinAt

lemma contDiff_slice {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : ContDiff ℝ ∞ (u t) :=
  hu.comp_contDiff (f := fun x : T3 => (t, x)) (contDiff_const.prodMk contDiff_id)
    (fun _ => ⟨ht, trivial⟩)

lemma fderiv_slice {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : T3) :
    fderiv ℝ (u t) x = (D T u (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ T3) := by
  have h1 : HasFDerivAt (fun y : T3 => (t, y)) (ContinuousLinearMap.inr ℝ ℝ T3) x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have := (hasFDerivWithinAt_D hu ⟨ht, trivial⟩).comp x h1.hasFDerivWithinAt
    (s := univ) (fun _ _ => ⟨ht, trivial⟩)
  exact (this.hasFDerivAt Filter.univ_mem).fderiv

lemma hasDerivWithinAt_time {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : T3) :
    HasDerivWithinAt (fun s => u s x) (D T u (t, x) (1, 0)) (Icc (0 : ℝ) T) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : T3)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have := (hasFDerivWithinAt_D hu ⟨ht, trivial⟩).comp_hasDerivWithinAt t h1.hasDerivWithinAt
    (fun _ hs => ⟨hs, trivial⟩)
  simpa using this

lemma derivWithin_time (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : T3) :
    derivWithin (fun s => u s x) (Icc (0 : ℝ) T) t = D T u (t, x) (1, 0) :=
  (hasDerivWithinAt_time hu ht x).derivWithin ((uniqueDiffOn_Icc hT) t ht)

lemma continuousOn_U : ContinuousOn (fun q : ℝ × T3 => u q.1 q.2) (S T) := hu.continuousOn

end regularity


lemma torusIntegral_congr {f g : E → ℝ} {t t' : ℝ}
    (h : ∀ a b c, f (t, a, b, c) = g (t', a, b, c)) : torusIntegral f t = torusIntegral g t' := by
  simp only [WeightedEnstrophy.Torus.torusIntegral, WeightedEnstrophy.Torus.i2,
    WeightedEnstrophy.Torus.i3, h]

section energy

variable {T : ℝ} {u v : TimeDependentVelocity}

/-- `|w|²` with `w = u − v`. -/
noncomputable def Gf (u v : TimeDependentVelocity) (q : ℝ × T3) : ℝ :=
  ⟪u q.1 q.2 - v q.1 q.2, u q.1 q.2 - v q.1 q.2⟫

/-- `2⟨w, ∂ₜw⟩`. -/
noncomputable def Gd (T : ℝ) (u v : TimeDependentVelocity) (q : ℝ × T3) : ℝ :=
  2 * ⟪u q.1 q.2 - v q.1 q.2, D T u q (1, 0) - D T v q (1, 0)⟫

/-- The difference energy, through the tangent-line extension in time. -/
noncomputable def energy (T : ℝ) (u v : TimeDependentVelocity) (t : ℝ) : ℝ :=
  torusIntegral (fun q => tangentExt T (fun s => Gf u v (s, toT3 q.2.1 q.2.2.1 q.2.2.2))
    (fun s => Gd T u v (s, toT3 q.2.1 q.2.2.1 q.2.2.2)) q.1) t

/-- Its derivative. -/
noncomputable def energy' (T : ℝ) (u v : TimeDependentVelocity) (t : ℝ) : ℝ :=
  torusIntegral (fun q => Gd T u v (cl T q.1, toT3 q.2.1 q.2.2.1 q.2.2.2)) t

variable (hT : 0 < T) (hu : ContDiffOn ℝ ∞ (fun q : ℝ × T3 => u q.1 q.2) (S T))
  (hv : ContDiffOn ℝ ∞ (fun q : ℝ × T3 => v q.1 q.2) (S T))
include hT hu hv

omit hT in
lemma continuousOn_Gf : ContinuousOn (Gf u v) (S T) := by
  have := (continuousOn_U hu).sub (continuousOn_U hv)
  exact this.inner this

lemma continuousOn_Gd : ContinuousOn (Gd T u v) (S T) := by
  have h1 := (continuousOn_U hu).sub (continuousOn_U hv)
  have c : ContinuousOn (fun _ : ℝ × T3 => ((1 : ℝ), (0 : T3))) (S T) := continuousOn_const
  have h2 := ((continuousOn_D hu hT).clm_apply c).sub ((continuousOn_D hv hT).clm_apply c)
  exact continuousOn_const.mul (h1.inner h2)

omit hu hv in
lemma continuous_clamped {G : ℝ × T3 → ℝ} (hG : ContinuousOn G (S T)) :
    Continuous fun q : E => G (cl T q.1, toT3 q.2.1 q.2.2.1 q.2.2.2) :=
  hG.comp_continuous (((continuous_cl T).comp continuous_fst).prodMk continuous_toT3)
    fun _ => ⟨cl_mem hT.le _, trivial⟩

omit hT in
lemma hasDerivWithinAt_Gf {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (x : T3) :
    HasDerivWithinAt (fun r => Gf u v (r, x)) (Gd T u v (s, x)) (Icc (0 : ℝ) T) s := by
  have hw := (hasDerivWithinAt_time hu hs x).sub (hasDerivWithinAt_time hv hs x)
  have := hw.inner ℝ hw
  unfold Gf Gd
  convert this using 1
  simp only [Pi.sub_apply]; rw [real_inner_comm (u s x - v s x)]; ring

theorem hasDerivAt_energy (t : ℝ) : HasDerivAt (energy T u v) (energy' T u v t) t := by
  have h1 := continuous_clamped hT (continuousOn_Gf hu hv)
  have h2 := continuous_clamped hT (continuousOn_Gd hT hu hv)
  have hf : Continuous fun q : E => tangentExt T (fun s => Gf u v (s, toT3 q.2.1 q.2.2.1 q.2.2.2))
      (fun s => Gd T u v (s, toT3 q.2.1 q.2.2.1 q.2.2.2)) q.1 := by
    unfold tangentExt
    exact h1.add ((continuous_fst.sub ((continuous_cl T).comp continuous_fst)).mul h2)
  have hd : ∀ t a b c, HasDerivAt
      (fun s => tangentExt T (fun s => Gf u v (s, toT3 a b c)) (fun s => Gd T u v (s, toT3 a b c)) s)
      (Gd T u v (cl T t, toT3 a b c)) t := fun t a b c =>
    hasDerivAt_ext hT (fun s hs => hasDerivWithinAt_Gf hu hv hs _) t
  unfold energy energy'
  exact hasDerivAt_torusIntegral hf h2 hd t

omit hT hu hv in
lemma energy_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    energy T u v t = cellIntegral fun x => Gf u v (t, x) :=
  torusIntegral_congr fun a b c => by simp [tangentExt, cl_of_mem ht, lift]

omit hT hu hv in
lemma energy'_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    energy' T u v t = cellIntegral fun x => Gd T u v (t, x) :=
  torusIntegral_congr fun a b c => by simp [cl_of_mem ht, lift]

end energy

/-! ### Unit-cell facts -/

lemma cellIntegral_mono_on {g h : T3 → ℝ} (hg : Continuous g) (hh : Continuous h)
    (H : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, ∀ c ∈ Icc (0 : ℝ) 1,
      g (toT3 a b c) ≤ h (toT3 a b c)) : cellIntegral g ≤ cellIntegral h :=
  torusIntegral_mono_on (continuous_lift hg) (continuous_lift hh) 0 H

lemma cellIntegral_zero : cellIntegral (fun _ => (0 : ℝ)) = 0 := by
  have := cellIntegral_const_mul 0 (fun _ => (0 : ℝ)); simpa using this

/-- Every point of `ℝ³` is a point of the unit cell plus a lattice vector. -/
lemma exists_cell (x : T3) : ∃ a ∈ Icc (0 : ℝ) 1, ∃ b ∈ Icc (0 : ℝ) 1, ∃ c ∈ Icc (0 : ℝ) 1,
    ∃ k : Fin 3 → ℤ, x = toT3 a b c + intVecToT3 k := by
  have hf : ∀ r : ℝ, Int.fract r ∈ Icc (0 : ℝ) 1 := fun r =>
    ⟨Int.fract_nonneg r, (Int.fract_lt_one r).le⟩
  refine ⟨_, hf (x 0), _, hf (x 1), _, hf (x 2), fun i => ⌊x i⌋, ?_⟩
  ext i; fin_cases i <;> simp [intVecToT3, Fin.sum_univ_three, stdBasisVec, Int.fract_add_floor]

lemma isZ3Periodic_fderiv {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α] {g : T3 → α}
    (hg : IsZ3Periodic g) : IsZ3Periodic (fderiv ℝ g) := by
  intro x k
  rw [← fderiv_comp_add_right]
  congr 1; funext y; exact hg y k

lemma continuous_toT3' : Continuous fun r : ℝ × ℝ × ℝ => toT3 r.1 r.2.1 r.2.2 :=
  continuous_toT3.comp ((continuous_const.prodMk continuous_id :
    Continuous fun r : ℝ × ℝ × ℝ => ((0 : ℝ), r)))

/-! ### The pointwise inequality -/

section pointwise

variable {ν : ℝ} {u₀ : VelocityField} {T : ℝ} {u v : TimeDependentVelocity}
  {p q : TimeDependentPressure}

lemma contDiff_slice_p (hp : ContDiffOn ℝ ∞ (fun q : ℝ × T3 => p q.1 q.2) (S T)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) : ContDiff ℝ ∞ (p t) :=
  hp.comp_contDiff (f := fun x : T3 => (t, x)) (contDiff_const.prodMk contDiff_id)
    (fun _ => ⟨ht, trivial⟩)

/-- The three divergence-form sums. -/
noncomputable def S1 (a w : VelocityField) (x : T3) : ℝ :=
  ∑ k : Fin 3, fderiv ℝ (fun y => ⟪w y, w y⟫ * a y k) x (e k)
noncomputable def S2 (w : VelocityField) (x : T3) : ℝ :=
  ∑ k : Fin 3, fderiv ℝ (fun y => ⟪w y, fderiv ℝ w y (e k)⟫) x (e k)
noncomputable def SP (π : T3 → ℝ) (w : VelocityField) (x : T3) : ℝ :=
  ∑ k : Fin 3, fderiv ℝ (fun y => π y * w y k) x (e k)

variable (hν : 0 ≤ ν) (hu : IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p)
  (hv : IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T v q)
include hu hv

theorem Gd_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {C : ℝ} (x : T3)
    (hC : ‖fderiv ℝ (v t) x‖ ≤ C) (hν : 0 ≤ ν) :
    Gd T u v (t, x) ≤ -1 * S1 (u t) (u t - v t) x + 2 * C * ⟪(u t - v t) x, (u t - v t) x⟫ +
      2 * ν * S2 (u t - v t) x + -2 * SP (p t) (u t - v t) x + 2 * SP (q t) (u t - v t) x := by
  obtain ⟨hT, -, -, cu, cp, pdeu, divu, -⟩ := hu
  obtain ⟨-, -, -, cv, cq, pdev, divv, -⟩ := hv
  set a := u t; set b := v t; set w := a - b with hw_def
  have sa := contDiff_slice cu ht; have sb := contDiff_slice cv ht
  have sw : ContDiff ℝ ∞ w := sa.sub sb
  have da := sa.differentiable (by simp); have db := sb.differentiable (by simp)
  have dw := sw.differentiable (by simp)
  have dp := (contDiff_slice_p cp ht).differentiable (by simp)
  have dq := (contDiff_slice_p cq ht).differentiable (by simp)
  have pu : derivWithin (fun s => u s x) (Icc 0 T) t =
      ν • laplacian a x - pressureGradient (p t) x - convective a a x := by
    rw [eq_sub_iff_add_eq]; simpa using pdeu t ht x
  have pv : derivWithin (fun s => v s x) (Icc 0 T) t =
      ν • laplacian b x - pressureGradient (q t) x - convective b b x := by
    rw [eq_sub_iff_add_eq]; simpa using pdev t ht x
  have eq1 : Gd T u v (t, x) = 2 * (ν * ⟪w x, laplacian w x⟫ - ⟪w x, gradient (p t) x⟫ +
      ⟪w x, gradient (q t) x⟫ - ⟪w x, fderiv ℝ w x (a x)⟫ - ⟪w x, fderiv ℝ b x (w x)⟫) := by
    have hl := laplacian_sub (sa.of_le ENat.LEInfty.out) (sb.of_le ENat.LEInfty.out) x
    have hc := convective_sub da db x
    unfold Gd
    simp only
    rw [← derivWithin_time cu hT ht x, ← derivWithin_time cv hT ht x, pu, pv]
    have : ν • laplacian a x - pressureGradient (p t) x - convective a a x -
        (ν • laplacian b x - pressureGradient (q t) x - convective b b x) =
        ν • laplacian w x - gradient (p t) x + gradient (q t) x -
          (fderiv ℝ w x (a x) + fderiv ℝ b x (w x)) := by
      rw [hl, ← hc, smul_sub]; simp only [pressureGradient]; abel
    rw [this]
    simp only [inner_sub_right, inner_add_right, inner_smul_right]
    simp only [hw_def, Pi.sub_apply]
    ring
  have hdiva : div a x = 0 := divu t ht x
  have hdivw : div w x = 0 := by rw [div_sub da db, hdiva, divv t ht x, sub_zero]
  have i1 := two_inner_convective dw da x
  have i2 := inner_laplacian (sw.of_le ENat.LEInfty.out) x
  have i3 := inner_gradient dw dp x
  have i4 := inner_gradient dw dq x
  have hN : 0 ≤ ∑ k : Fin 3, ‖fderiv ℝ w x (e k)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs : -⟪w x, fderiv ℝ b x (w x)⟫ ≤ C * ⟪w x, w x⟫ := by
    rw [real_inner_self_eq_norm_sq]
    have h1 := abs_real_inner_le_norm (w x) (fderiv ℝ b x (w x))
    have h2 := (fderiv ℝ b x).le_opNorm (w x)
    have h3 : ‖w x‖ * ‖fderiv ℝ b x (w x)‖ ≤ ‖w x‖ * (C * ‖w x‖) :=
      mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _)))
        (norm_nonneg _)
    nlinarith [neg_abs_le ⟪w x, fderiv ℝ b x (w x)⟫]
  have hνN := mul_nonneg hν hN
  rw [eq1]
  unfold S1 S2 SP
  rw [hdiva] at i1; rw [hdivw] at i3 i4
  nlinarith [i1, i2, i3, i4, hcs, hνN]

end pointwise

/-! ### Integration of the pointwise inequality -/

section main

variable {ν : ℝ} {u₀ : VelocityField} {T : ℝ} {u v : TimeDependentVelocity}
  {p q : TimeDependentPressure}

lemma continuous_divsum {φ : Fin 3 → T3 → ℝ} (hφ : ∀ k, ContDiff ℝ 1 (φ k)) :
    Continuous fun x => ∑ k : Fin 3, fderiv ℝ (φ k) x (e k) :=
  continuous_finset_sum _ fun k _ =>
    ((hφ k).continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem cellIntegral_rhs (hu : IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p)
    (hv : IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T v q) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) (C : ℝ) :
    cellIntegral (fun x => -1 * S1 (u t) (u t - v t) x +
      2 * C * ⟪(u t - v t) x, (u t - v t) x⟫ + 2 * ν * S2 (u t - v t) x +
      -2 * SP (p t) (u t - v t) x + 2 * SP (q t) (u t - v t) x) =
      2 * C * cellIntegral (fun x => Gf u v (t, x)) := by
  obtain ⟨-, peru, perp, cu, cp, -, -, -⟩ := hu
  obtain ⟨-, perv, perq, cv, cq, -, -, -⟩ := hv
  set a := u t; set b := v t
  have sa := contDiff_slice cu ht; have sb := contDiff_slice cv ht
  have sw : ContDiff ℝ ∞ (a - b) := sa.sub sb
  have sp := contDiff_slice_p cp ht; have sq := contDiff_slice_p cq ht
  have pa : IsZ3Periodic a := peru t ht
  have pb : IsZ3Periodic b := perv t ht
  have pw : IsZ3Periodic (a - b) := fun x k => by simp [pa x k, pb x k]
  have pp : IsZ3Periodic (p t) := perp t ht
  have pq : IsZ3Periodic (q t) := perq t ht
  have w1 : ContDiff ℝ 1 (a - b) := sw.of_le ENat.LEInfty.out
  have coord : ∀ {f : VelocityField}, ContDiff ℝ 1 f → ∀ k : Fin 3,
      ContDiff ℝ 1 (fun y => f y k) := fun hf k =>
    (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp hf
  have h1 : ∀ k : Fin 3, ContDiff ℝ 1 (fun y => ⟪(a - b) y, (a - b) y⟫ * a y k) := fun k =>
    (w1.inner ℝ w1).mul (coord (sa.of_le ENat.LEInfty.out) k)
  have h2 : ∀ k : Fin 3, ContDiff ℝ 1 (fun y => ⟪(a - b) y, fderiv ℝ (a - b) y (e k)⟫) :=
    fun k => w1.inner ℝ ((sw.fderiv_right (m := 1) (by norm_cast)).clm_apply contDiff_const)
  have h3 : ∀ {π : T3 → ℝ}, ContDiff ℝ ∞ π → ∀ k : Fin 3,
      ContDiff ℝ 1 (fun y => π y * (a - b) y k) := fun hπ k =>
    (hπ.of_le ENat.LEInfty.out).mul (coord w1 k)
  have z1 : cellIntegral (S1 a (a - b)) = 0 :=
    cellIntegral_sum_fderiv_eq_zero h1 fun k x j => by simp [pw x j, pa x j]
  have z2 : cellIntegral (S2 (a - b)) = 0 :=
    cellIntegral_sum_fderiv_eq_zero h2 fun k x j => by
      rw [pw x j, isZ3Periodic_fderiv pw x j]
  have z3 : ∀ {π : T3 → ℝ}, ContDiff ℝ ∞ π → IsZ3Periodic π →
      cellIntegral (SP π (a - b)) = 0 := fun hπ hpπ =>
    cellIntegral_sum_fderiv_eq_zero (h3 hπ) fun k x j => by simp [hpπ x j, pw x j]
  have c1 : Continuous (S1 a (a - b)) := continuous_divsum h1
  have c2 : Continuous (S2 (a - b)) := continuous_divsum h2
  have z3' := z3 sp pp; have z4' := z3 sq pq
  have c3 : Continuous (SP (p t) (a - b)) := continuous_divsum (h3 sp)
  have c4 : Continuous (SP (q t) (a - b)) := continuous_divsum (h3 sq)
  have cw : Continuous fun x => ⟪(a - b) x, (a - b) x⟫ := w1.continuous.inner w1.continuous
  generalize S1 a (a - b) = f1 at c1 z1 ⊢
  generalize S2 (a - b) = f2 at c2 z2 ⊢
  generalize SP (p t) (a - b) = f3 at c3 z3' ⊢
  generalize SP (q t) (a - b) = f4 at c4 z4' ⊢
  generalize hW : (fun x => ⟪(a - b) x, (a - b) x⟫) = W at cw
  have hW' : ∀ x, ⟪(a - b) x, (a - b) x⟫ = W x := fun x => by rw [← hW]
  simp only [hW']
  rw [cellIntegral_add (by fun_prop) (by fun_prop), cellIntegral_add (by fun_prop) (by fun_prop),
    cellIntegral_add (by fun_prop) (by fun_prop), cellIntegral_add (by fun_prop) (by fun_prop),
    cellIntegral_const_mul, cellIntegral_const_mul, cellIntegral_const_mul,
    cellIntegral_const_mul, cellIntegral_const_mul, z1, z2, z3' , z4']
  simp [Gf, a, b, ← hW]

/-- **Proved (for `ν ≥ 0`):** the periodic energy inequality for the difference of two
classical solutions with the same data. -/
theorem periodicEnergyDifferenceEstimate (hν : 0 ≤ ν) : PeriodicEnergyDifferenceEstimate ν := by
  intro u₀ T u v p q hu hv
  have hT := hu.1
  have cu := hu.2.2.2.1; have cv := hv.2.2.2.1
  -- a bound `C` for `‖D v‖` on `[0, T] × cell`
  set K : Set (ℝ × T3) := Icc (0 : ℝ) T ×ˢ ((fun r : ℝ × ℝ × ℝ => toT3 r.1 r.2.1 r.2.2) ''
    (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
  have hK : IsCompact K := isCompact_Icc.prod
    ((isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).image continuous_toT3')
  have hKS : K ⊆ S T := fun z hz => ⟨hz.1, trivial⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn ((continuousOn_D cv hT).mono hKS)
  have hCb : ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
      ∀ c ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ (v t) (toT3 a b c)‖ ≤ C := by
    intro t ht a ha b hb c hc
    rw [fderiv_slice cv ht]
    refine ((D T v _).opNorm_comp_le _).trans ?_
    have h1 := hC (t, toT3 a b c) ⟨ht, ⟨(a, b, c), ⟨ha, hb, hc⟩, rfl⟩⟩
    have h2 : ‖ContinuousLinearMap.inr ℝ ℝ T3‖ ≤ 1 := ContinuousLinearMap.norm_inr_le_one ℝ ℝ T3
    nlinarith [norm_nonneg (D T v (t, toT3 a b c))]
  refine ⟨energy T u v, energy' T u v, 2 * C, ?_, ?_, ?_, ?_, ?_⟩
  · exact (continuous_iff_continuousAt.2 fun t =>
      (hasDerivAt_energy hT cu cv t).continuousAt).continuousOn
  · exact fun t _ => (hasDerivAt_energy hT cu cv t).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Icc (0 : ℝ) T := Ico_subset_Icc_self ht
    rw [energy'_eq ht', energy_eq ht', ← cellIntegral_rhs hu hv ht' C]
    have cGd : Continuous fun x => Gd T u v (t, x) :=
      (continuousOn_Gd hT cu cv).comp_continuous (continuous_const.prodMk continuous_id)
        fun _ => ⟨ht', trivial⟩
    have cp := hu.2.2.2.2.1; have cq := hv.2.2.2.2.1
    have sa := contDiff_slice cu ht'; have sb := contDiff_slice cv ht'
    have w1 : ContDiff ℝ 1 (u t - v t) := (sa.sub sb).of_le ENat.LEInfty.out
    have coord : ∀ {f : VelocityField}, ContDiff ℝ 1 f → ∀ k : Fin 3,
        ContDiff ℝ 1 (fun y => f y k) := fun hf k =>
      (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp hf
    have c1 : Continuous (S1 (u t) (u t - v t)) := continuous_divsum fun k =>
      (w1.inner ℝ w1).mul (coord (sa.of_le ENat.LEInfty.out) k)
    have c2 : Continuous (S2 (u t - v t)) := continuous_divsum fun k =>
      w1.inner ℝ (((sa.sub sb).fderiv_right (m := 1) (by norm_cast)).clm_apply contDiff_const)
    have c3 : ∀ {π : T3 → ℝ}, ContDiff ℝ ∞ π → Continuous (SP π (u t - v t)) := fun hπ =>
      continuous_divsum fun k => (hπ.of_le ENat.LEInfty.out).mul (coord w1 k)
    have cw : Continuous fun x => ⟪(u t - v t) x, (u t - v t) x⟫ :=
      w1.continuous.inner w1.continuous
    have c3p := c3 (contDiff_slice_p cp ht'); have c3q := c3 (contDiff_slice_p cq ht')
    have cR : Continuous fun x => -1 * S1 (u t) (u t - v t) x +
      2 * C * ⟪(u t - v t) x, (u t - v t) x⟫ + 2 * ν * S2 (u t - v t) x +
      -2 * SP (p t) (u t - v t) x + 2 * SP (q t) (u t - v t) x :=
      ((((continuous_const.mul c1).add (continuous_const.mul cw)).add
        (continuous_const.mul c2)).add (continuous_const.mul c3p)).add (continuous_const.mul c3q)
    refine cellIntegral_mono_on cGd cR fun a ha b hb c hc => ?_
    exact Gd_le hu hv ht' _ (hCb t ht' a ha b hb c hc) hν
  · have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
    rw [energy_eq h0]
    have : (fun x => Gf u v (0, x)) = fun _ => (0 : ℝ) := by
      funext x; simp [Gf, hu.2.2.2.2.2.2.2 x, hv.2.2.2.2.2.2.2 x]
    rw [this, cellIntegral_zero]
  · intro t ht hle
    rw [energy_eq ht] at hle
    have cG : Continuous fun x => Gf u v (t, x) :=
      (continuousOn_Gf cu cv).comp_continuous (continuous_const.prodMk continuous_id)
        fun _ => ⟨ht, trivial⟩
    have hz := eq_zero_of_torusIntegral_nonpos (continuous_lift cG) 0
      (fun a _ b _ c _ => real_inner_self_nonneg) hle
    have pw : IsZ3Periodic (u t - v t) := fun x k => by
      simp [hu.2.1 t ht x k, hv.2.1 t ht x k]
    funext x
    obtain ⟨a, ha, b, hb, c, hc, k, rfl⟩ := exists_cell x
    have hz' := hz a ha b hb c hc
    simp only [lift, Gf] at hz'
    have := inner_self_eq_zero.1 hz'
    have key : (u t - v t) (toT3 a b c + intVecToT3 k) = 0 := by
      rw [pw]; exact this
    exact sub_eq_zero.1 key

end main

end PeriodicNSContinuation.Corrected
