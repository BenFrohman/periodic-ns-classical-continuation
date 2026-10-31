/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.Continuation

/-!
# Splitting `PeriodicBKMHsControl` (names coined)

* `gronwall_of_hasDerivAt` — **proved**: differential Grönwall with a continuous coefficient.
* `PeriodicTameHsInequality ν s C` — **hypothesis** (Kato–Ponce commutator / tame energy estimate):
  `d/dt ‖u‖²_{H^s} ≤ C ‖∇u‖_∞ ‖u‖²_{H^s}` along smooth solutions.
* `PeriodicSupNormContinuity ν` — now **proved** in `BKMPieces.lean` (`periodicSupNormContinuity`): `t ↦ ‖∇u(t)‖_∞`
  and `t ↦ ‖ω(t)‖_∞` are continuous on `[0,T']`.
* `PeriodicLogSobolevBKM s K` — **hypothesis** (Brezis–Gallouet / BKM log inequality):
  `‖∇v‖_∞ ≤ K (1 + ‖ω‖_∞ (1 + log (1 + ‖v‖²_{H^s})))`.
* `periodicGradHsControl` — **proved from the first two**: `∫₀^{T*} ‖∇u‖_∞ < ∞ ⇒ H^s` bounded.
* `periodicBKMHsControl_of_tame_log` — **proved from all three**: `PeriodicBKMHsControl ν s`.
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D
open scoped ContDiff

namespace PeriodicNSContinuation

open Corrected

/-- Coined. `‖∇v‖_∞` as `⨆ x, ‖Dv(x)‖` (operator norm). -/
def gradSupNorm (v : VelocityField) : ℝ := ⨆ x, ‖fderiv ℝ v x‖

/-- Coined. `‖v‖²_{H^s}` via Fourier coefficients. -/
def hsSq (s : ℝ) (v : VelocityField) : ℝ :=
  TorusFourierNS.hsNormField s (fourierCoeffVF v) ^ 2

lemma gradSupNorm_nonneg (v : VelocityField) : 0 ≤ gradSupNorm v :=
  Real.iSup_nonneg fun _ => norm_nonneg _

lemma hsSq_nonneg (s : ℝ) (v : VelocityField) : 0 ≤ hsSq s v := sq_nonneg _

/-- Coined. **Hypothesis (classical, Kato–Ponce).** For some `C = C(s)` this is true for `s > 5/2`:
the `H^s` energy identity, the vanishing of the pressure term (`div u = 0`), the sign of the
viscous term and the commutator bound `‖[J^s, u·∇]u‖_{L²} ≤ C ‖∇u‖_∞ ‖u‖_{H^s}`.
Not vacuous: smooth solutions exist (`periodicLocalSolution_quant`). -/
def PeriodicTameHsInequality (ν s C : ℝ) : Prop :=
  0 < ν → ∀ (u₀ : VelocityField) (u : TimeDependentVelocity) (p : TimeDependentPressure) (T' : ℝ),
    IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T' u p →
    ContinuousOn (fun t => hsSq s (u t)) (Icc 0 T') ∧
    ∀ t ∈ Ioo 0 T', ∃ d, HasDerivAt (fun t => hsSq s (u t)) d t ∧
      d ≤ C * gradSupNorm (u t) * hsSq s (u t)

/-- Coined. **Proved** in `BKMPieces.lean` (`periodicSupNormContinuity`): sup norms of `∇u` and `ω` are continuous
in time for a solution smooth on `[0,T'] × ℝ³` and periodic in space. -/
def PeriodicSupNormContinuity (ν : ℝ) : Prop :=
  0 < ν → ∀ (u₀ : VelocityField) (u : TimeDependentVelocity) (p : TimeDependentPressure) (T' : ℝ),
    IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T' u p →
    ContinuousOn (fun t => gradSupNorm (u t)) (Icc 0 T') ∧
    ContinuousOn (fun t => vorticity_sup_norm (vorticity (u t))) (Icc 0 T')

/-- Coined. **Hypothesis (Brezis–Gallouet / Beale–Kato–Majda 1984).** True for some `K = K(s)` when
`s > 5/2`: on the unit torus `‖ω‖_{L²} ≤ ‖ω‖_∞`, the mean mode does not change `∇v` or `ω`, and
`log(1+x) ≤ (log 2 + log(1+x²))/2`. -/
def PeriodicLogSobolevBKM (s K : ℝ) : Prop :=
  ∀ v : VelocityField, IsPeriodicSmoothInitialData v →
    gradSupNorm v ≤ K * (1 + vorticity_sup_norm (vorticity v) * (1 + Real.log (1 + hsSq s v)))

/-- **Proved.** Differential Grönwall with a continuous coefficient. -/
theorem gronwall_of_hasDerivAt {f a : ℝ → ℝ} {T' : ℝ}
    (hf : ContinuousOn f (Icc 0 T')) (ha : ContinuousOn a (Icc 0 T'))
    (hd : ∀ t ∈ Ioo 0 T', ∃ d, HasDerivAt f d t ∧ d ≤ a t * f t) :
    ∀ t ∈ Icc 0 T', f t ≤ f 0 * Real.exp (∫ τ in (0:ℝ)..t, a τ) := by
  intro t ht
  have hT' : 0 ≤ T' := ht.1.trans ht.2
  set G := fun x => ∫ τ in (0:ℝ)..x, a τ
  have hG : ContinuousOn G (Icc 0 T') := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := T')
      (f := a) (by rw [uIcc_of_le hT']; exact ha.integrableOn_Icc)
    rwa [uIcc_of_le hT'] at this
  have hGd : ∀ x ∈ Ioo 0 T', HasDerivAt G (a x) x := by
    intro x hx
    apply intervalIntegral.integral_hasDerivAt_right
    · exact (ha.mono (by rw [uIcc_of_le hx.1.le]; exact Icc_subset_Icc le_rfl hx.2.le)).intervalIntegrable
    · exact (ha.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx
    · exact ha.continuousAt (Icc_mem_nhds hx.1 hx.2)
  set h := fun x => f x * Real.exp (-G x)
  have hhd : ∀ x ∈ Ioo 0 T', ∃ e, HasDerivAt h e x ∧ e ≤ 0 := by
    intro x hx
    obtain ⟨d, hd1, hd2⟩ := hd x hx
    refine ⟨d * Real.exp (-G x) + f x * (Real.exp (-G x) * -a x),
      hd1.mul ((hGd x hx).neg.exp), ?_⟩
    have := Real.exp_pos (-G x)
    nlinarith
  have hanti : AntitoneOn h (Icc 0 T') := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T')
    · exact hf.mul (hG.neg.rexp)
    · rw [interior_Icc]; intro x hx
      obtain ⟨e, he, _⟩ := hhd x hx; exact he.differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro x hx
      obtain ⟨e, he, he'⟩ := hhd x hx; rw [he.deriv]; exact he'
  have h0 : h t ≤ h 0 := hanti ⟨le_rfl, hT'⟩ ht ht.1
  have hG0 : G 0 = 0 := intervalIntegral.integral_same
  simp only [h, hG0, neg_zero, Real.exp_zero, mul_one] at h0
  have : f t = f t * Real.exp (-G t) * Real.exp (G t) := by
    rw [mul_assoc, ← Real.exp_add]; simp
  rw [this]
  exact mul_le_mul_of_nonneg_right h0 (Real.exp_pos _).le

/-- Coined. **The easier classical step**, as a Prop: `∫₀^{T*} ‖∇u‖_∞ < ∞` bounds `‖u‖_{H^s}`. -/
def PeriodicGradHsControl (ν s : ℝ) : Prop :=
  0 < ν → ∀ u₀ : VelocityField, IsPeriodicSmoothInitialData u₀ →
    ∀ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      IsPeriodicMaximalSolution ν u₀ u p →
      ∀ T : ℝ, periodicTstar ν u₀ = (T : EReal) →
        IntegrableOn (fun t => gradSupNorm (u t)) (Icc 0 T) →
        ∃ M : ℝ, ∀ t ∈ Ico (0:ℝ) T, TorusFourierNS.hsNormField s (fourierCoeffVF (u t)) ≤ M

/-- Shared step: for `t ∈ Ico 0 T`, a solution on `[0, (t+T)/2]` containing `t`. -/
lemma sol_around {ν : ℝ} {u₀ : VelocityField} {u : TimeDependentVelocity}
    {p : TimeDependentPressure} (hm : IsPeriodicMaximalSolution ν u₀ u p) {T : ℝ}
    (hT : periodicTstar ν u₀ = (T : EReal)) {t : ℝ} (ht : t ∈ Ico (0:ℝ) T) :
    IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) ((t + T) / 2) u p ∧
      t ∈ Icc (0:ℝ) ((t + T) / 2) ∧ (t + T) / 2 ≤ T := by
  refine ⟨hm _ (by linarith [ht.1, ht.2]) (by rw [hT]; exact_mod_cast (by linarith [ht.2])),
    ⟨ht.1, by linarith [ht.2]⟩, by linarith [ht.2]⟩

lemma hsNorm_le_of_hsSq_le {s B : ℝ} {v : VelocityField} (h : hsSq s v ≤ B) :
    TorusFourierNS.hsNormField s (fourierCoeffVF v) ≤ Real.sqrt B := by
  have h0 : 0 ≤ TorusFourierNS.hsNormField s (fourierCoeffVF v) := by
    unfold TorusFourierNS.hsNormField; exact Real.sqrt_nonneg _
  rw [← Real.sqrt_sq h0]; exact Real.sqrt_le_sqrt h

lemma u_zero {ν : ℝ} {u₀ : VelocityField} {u : TimeDependentVelocity}
    {p : TimeDependentPressure} {T' : ℝ}
    (h : IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T' u p) : u 0 = u₀ :=
  funext h.2.2.2.2.2.2.2

lemma integral_le_of_nonneg {g : ℝ → ℝ} {t T : ℝ} (ht : t ∈ Ico (0:ℝ) T)
    (hg : ∀ x, 0 ≤ g x) (hi : IntegrableOn g (Icc 0 T)) :
    ∫ τ in (0:ℝ)..t, g τ ≤ ∫ τ in (0:ℝ)..T, g τ :=
  intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2.le
    (Eventually.of_forall fun x => hg x)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le (ht.1.trans ht.2.le)).2 hi)

/-- **Proved** from the tame inequality and sup-norm continuity (Grönwall). -/
theorem periodicGradHsControl {ν s C : ℝ} (hC : 0 ≤ C) (htame : PeriodicTameHsInequality ν s C)
    (hcont : PeriodicSupNormContinuity ν) : PeriodicGradHsControl ν s := by
  intro hν u₀ _ u p hm T hT hint
  refine ⟨Real.sqrt (hsSq s u₀ * Real.exp (C * ∫ τ in (0:ℝ)..T, gradSupNorm (u τ))), ?_⟩
  intro t ht
  obtain ⟨hsol, htI, -⟩ := sol_around hm hT ht
  obtain ⟨hyc, hyd⟩ := htame hν u₀ u p _ hsol
  have hg := (hcont hν u₀ u p _ hsol).1
  have key := gronwall_of_hasDerivAt (a := fun t => C * gradSupNorm (u t)) hyc
    (continuousOn_const.mul hg) hyd t htI
  apply hsNorm_le_of_hsSq_le
  refine key.trans ?_
  rw [u_zero hsol, intervalIntegral.integral_const_mul]
  gcongr
  · exact hsSq_nonneg _ _
  · exact integral_le_of_nonneg ht (fun x => gradSupNorm_nonneg (u x)) hint

/-- **Proved** from the tame inequality, sup-norm continuity and the log inequality
(Grönwall applied to `1 + log (1 + ‖u‖²_{H^s})`). -/
theorem periodicBKMHsControl_of_tame_log {ν s C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (htame : PeriodicTameHsInequality ν s C) (hcont : PeriodicSupNormContinuity ν)
    (hlog : PeriodicLogSobolevBKM s K) : PeriodicBKMHsControl ν s := by
  intro hν u₀ _ u p hm T hT hint
  set wv := fun t => vorticity_sup_norm (vorticity (u t))
  set a := fun t => C * K * (1 + wv t)
  set f0 := 1 + Real.log (1 + hsSq s u₀)
  refine ⟨Real.sqrt (Real.exp (f0 * Real.exp (∫ τ in (0:ℝ)..T, a τ))), ?_⟩
  intro t ht
  obtain ⟨hsol, htI, -⟩ := sol_around hm hT ht
  obtain ⟨hyc, hyd⟩ := htame hν u₀ u p _ hsol
  have hwv := (hcont hν u₀ u p _ hsol).2
  set y := fun t => hsSq s (u t)
  have hy0 : ∀ t, 0 < 1 + y t := fun t => by linarith [hsSq_nonneg s (u t)]
  have hfc : ContinuousOn (fun t => 1 + Real.log (1 + y t)) (Icc 0 ((t + T) / 2)) :=
    continuousOn_const.add ((continuousOn_const.add hyc).log fun x _ => (hy0 x).ne')
  have hac : ContinuousOn a (Icc 0 ((t + T) / 2)) :=
    continuousOn_const.mul (continuousOn_const.add hwv)
  have hfd : ∀ x ∈ Ioo 0 ((t + T) / 2), ∃ d,
      HasDerivAt (fun t => 1 + Real.log (1 + y t)) d x ∧ d ≤ a x * (1 + Real.log (1 + y x)) := by
    intro x hx
    obtain ⟨d, hd1, hd2⟩ := hyd x hx
    refine ⟨d / (1 + y x), ((hd1.const_add 1).log (hy0 x).ne').const_add 1 |>.congr_deriv
      (by simp), ?_⟩
    have hxI : x ∈ Icc (0:ℝ) ((t + T) / 2) := Ioo_subset_Icc_self hx
    have hux : IsPeriodicSmoothInitialData (u x) :=
      ⟨contDiff_slice hsol.2.2.2.1 hxI, fun z => hsol.2.2.2.2.2.2.1 x hxI z, hsol.2.1 x hxI⟩
    have hl := hlog (u x) hux
    have hg0 := gradSupNorm_nonneg (u x)
    have hyx := hsSq_nonneg s (u x)
    have hL : 0 ≤ Real.log (1 + y x) := Real.log_nonneg (by linarith)
    have hwvx : 0 ≤ wv x := vorticity_sup_norm_nonneg _
    have hpos := hy0 x
    rw [div_le_iff₀ hpos]
    have h1 : d ≤ C * gradSupNorm (u x) * (1 + y x) := hd2.trans (by
      have : C * gradSupNorm (u x) * hsSq s (u x) ≤ C * gradSupNorm (u x) * (1 + y x) :=
        mul_le_mul_of_nonneg_left (by simp [y]) (mul_nonneg hC hg0)
      exact this)
    have h2 : C * gradSupNorm (u x) ≤ a x * (1 + Real.log (1 + y x)) := by
      have : C * gradSupNorm (u x) ≤ C * (K * (1 + wv x * (1 + Real.log (1 + y x)))) :=
        mul_le_mul_of_nonneg_left hl hC
      refine this.trans ?_
      simp only [a]
      have := mul_nonneg (mul_nonneg hC hK) (mul_nonneg hwvx hL)
      nlinarith [mul_nonneg hC hK]
    calc d ≤ C * gradSupNorm (u x) * (1 + y x) := h1
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 hpos.le
  have key := gronwall_of_hasDerivAt hfc hac hfd t htI
  have hf0 : (1 + Real.log (1 + y 0)) = f0 := by simp [y, f0, u_zero hsol]
  rw [hf0] at key
  have hf0pos : 0 ≤ f0 := by
    have := Real.log_nonneg (by linarith [hsSq_nonneg s u₀] : (1:ℝ) ≤ 1 + hsSq s u₀); linarith
  have hai : IntegrableOn a (Icc 0 T) :=
    ((integrableOn_const (by simp)).add hint).const_mul _
  have hint2 := integral_le_of_nonneg ht (g := a)
    (fun x => mul_nonneg (mul_nonneg hC hK) (by linarith [vorticity_sup_norm_nonneg (vorticity (u x))]))
    hai
  have key2 : 1 + Real.log (1 + y t) ≤ f0 * Real.exp (∫ τ in (0:ℝ)..T, a τ) :=
    key.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hint2) hf0pos)
  apply hsNorm_le_of_hsSq_le
  have : 1 + y t ≤ Real.exp (f0 * Real.exp (∫ τ in (0:ℝ)..T, a τ)) := by
    rw [← Real.exp_log (hy0 t)]; exact Real.exp_le_exp.2 (by linarith)
  show y t ≤ _; linarith

/-- **Conditional assembly.** `Clay_B_exact ν` from the three hypotheses plus the OPEN
`PeriodicBKMIntegrability ν`. Clay is not solved. -/
theorem clay_B_exact_of_tame_log {ν s C K : ℝ} (hs : 5 / 2 < s) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (htame : PeriodicTameHsInequality ν s C) (hcont : PeriodicSupNormContinuity ν)
    (hlog : PeriodicLogSobolevBKM s K) (hint : PeriodicBKMIntegrability ν) : Clay_B_exact ν :=
  clay_B_exact_of_hsControl ν s hs (periodicBKMHsControl_of_tame_log hC hK htame hcont hlog) hint

end PeriodicNSContinuation
