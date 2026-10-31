/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.PhysicalCommutator

/-!
# Kato–Ponce toolkit on the unit cell

Calculus for smooth periodic scalar fields (`PerR`) integrated over the unit cell `[0,1]³`:
closure lemmas, Leibniz rule, integration by parts, and a Gagliardo–Nirenberg inequality.
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D TorusFourierNS
open scoped ContDiff

namespace PeriodicNSContinuation

local notation "Eq3" => EuclideanSpace.equiv (Fin 3) ℝ

/-- Coined. Integral of a scalar field over the unit cell `[0,1]³`. -/
def cellI (φ : T3 → ℝ) : ℝ := ∫ x in Icc (0 : Fin 3 → ℝ) 1, φ ((Eq3).symm x)

lemma PerR.cont {φ : T3 → ℝ} (h : PerR φ) : Continuous φ := h.1.continuous

lemma PerR.mul {φ ψ : T3 → ℝ} (h : PerR φ) (h' : PerR ψ) : PerR (fun y => φ y * ψ y) :=
  ⟨h.1.mul h'.1, fun x j => by simp only [h.2 x j, h'.2 x j]⟩

lemma PerR.add {φ ψ : T3 → ℝ} (h : PerR φ) (h' : PerR ψ) : PerR (fun y => φ y + ψ y) :=
  ⟨h.1.add h'.1, fun x j => by simp only [h.2 x j, h'.2 x j]⟩

lemma PerR.const_mul {φ : T3 → ℝ} (h : PerR φ) (c : ℝ) : PerR (fun y => c * φ y) :=
  ⟨contDiff_const.mul h.1, fun x j => by simp only [h.2 x j]⟩

lemma PerR.sum {ι : Type*} (s : Finset ι) {φ : ι → T3 → ℝ} (h : ∀ i, PerR (φ i)) :
    PerR (fun y => ∑ i ∈ s, φ i y) :=
  ⟨ContDiff.sum fun i _ => (h i).1, fun x j => by simp only [(h _).2 x j]⟩

lemma integrableOn_cell {φ : T3 → ℝ} (h : Continuous φ) :
    IntegrableOn (fun x => φ ((Eq3).symm x)) (Icc (0 : Fin 3 → ℝ) 1) :=
  (h.comp (Eq3).symm.continuous).continuousOn.integrableOn_compact isCompact_Icc

lemma cellI_add {φ ψ : T3 → ℝ} (h : Continuous φ) (h' : Continuous ψ) :
    cellI (fun y => φ y + ψ y) = cellI φ + cellI ψ :=
  integral_add (integrableOn_cell h) (integrableOn_cell h')

lemma cellI_const_mul (φ : T3 → ℝ) (c : ℝ) : cellI (fun y => c * φ y) = c * cellI φ :=
  integral_const_mul c _

lemma cellI_neg (φ : T3 → ℝ) : cellI (fun y => -φ y) = -cellI φ := integral_neg _

lemma cellI_sum {ι : Type*} (s : Finset ι) {φ : ι → T3 → ℝ} (h : ∀ i, Continuous (φ i)) :
    cellI (fun y => ∑ i ∈ s, φ i y) = ∑ i ∈ s, cellI (φ i) :=
  integral_finset_sum s fun i _ => integrableOn_cell (h i)

lemma cellI_mono {φ ψ : T3 → ℝ} (h : Continuous φ) (h' : Continuous ψ) (hle : ∀ y, φ y ≤ ψ y) :
    cellI φ ≤ cellI ψ :=
  setIntegral_mono (integrableOn_cell h) (integrableOn_cell h') fun x => hle _

lemma cellI_nonneg {φ : T3 → ℝ} (hle : ∀ y, 0 ≤ φ y) : 0 ≤ cellI φ :=
  setIntegral_nonneg measurableSet_Icc fun x _ => hle _

lemma cellI_pdR {φ : T3 → ℝ} (h : PerR φ) (j : Fin 3) : cellI (pdR j φ) = 0 := by
  have h0 := integral_pdC_eq_zero j (liftR φ) ((liftR_contDiff h.1).of_le (by simp))
    (liftR_add_single h j)
  have e : (fun x => pdC j (liftR φ) x) = fun x => ((pdR j φ ((Eq3).symm x) : ℝ) : ℂ) :=
    funext fun x => pdC_liftR (h.1.differentiable (by simp)) j x
  rw [e, integral_complex_ofReal] at h0
  exact_mod_cast h0

/-- Leibniz rule for `pdR`. -/
lemma pdR_mul {φ ψ : T3 → ℝ} (h : Differentiable ℝ φ) (h' : Differentiable ℝ ψ) (j : Fin 3) :
    pdR j (fun y => φ y * ψ y) = fun y => pdR j φ y * ψ y + φ y * pdR j ψ y := by
  funext y
  show fderiv ℝ (φ * ψ) y _ = _
  rw [((h y).hasFDerivAt.mul (h' y).hasFDerivAt).fderiv]
  simp [ContinuousLinearMap.add_apply, smul_eq_mul, pdR]; ring

lemma pdR_add {φ ψ : T3 → ℝ} (h : Differentiable ℝ φ) (h' : Differentiable ℝ ψ) (j : Fin 3) :
    pdR j (fun y => φ y + ψ y) = fun y => pdR j φ y + pdR j ψ y := by
  funext y; show fderiv ℝ (φ + ψ) y _ = _
  rw [((h y).hasFDerivAt.add (h' y).hasFDerivAt).fderiv]; rfl

lemma pdR_const_mul {φ : T3 → ℝ} (h : Differentiable ℝ φ) (c : ℝ) (j : Fin 3) :
    pdR j (fun y => c * φ y) = fun y => c * pdR j φ y := by
  funext y; simp only [pdR]; rw [((h y).hasFDerivAt.const_mul c).fderiv]; rfl

lemma pdR_sum {ι : Type*} (s : Finset ι) {φ : ι → T3 → ℝ} (h : ∀ i, Differentiable ℝ (φ i))
    (j : Fin 3) : pdR j (fun y => ∑ i ∈ s, φ i y) = fun y => ∑ i ∈ s, pdR j (φ i) y := by
  funext y; simp only [pdR]
  rw [fderiv_fun_sum fun i _ => h i y]; simp

/-- Schwarz: partial derivatives commute on smooth fields. -/
lemma pdR_comm {φ : T3 → ℝ} (h : ContDiff ℝ ∞ φ) (a b : Fin 3) :
    pdR a (pdR b φ) = pdR b (pdR a φ) := by
  funext y
  have hs := ((h.of_le (WithTop.coe_le_coe.2 (le_top : (2:ℕ∞) ≤ ⊤)) : ContDiff ℝ 2 φ).contDiffAt (x := y)).isSymmSndFDerivAt (by simp)
  show fderiv ℝ (fun z => fderiv ℝ φ z (EuclideanSpace.single b 1)) y (EuclideanSpace.single a 1) =
    fderiv ℝ (fun z => fderiv ℝ φ z (EuclideanSpace.single a 1)) y (EuclideanSpace.single b 1)
  have hd : ∀ w, fderiv ℝ (fun z => fderiv ℝ φ z w) y = fun v => fderiv ℝ (fderiv ℝ φ) y v w :=
    fun w => by
      funext v
      rw [fderiv_clm_apply ((h.fderiv_right (m := ∞) le_rfl).differentiable (by simp) y)
        (differentiableAt_const _)]
      simp
  rw [hd, hd]; exact hs _ _

/-- Integration by parts on the unit cell. -/
lemma cellI_ibp {φ ψ : T3 → ℝ} (h : PerR φ) (h' : PerR ψ) (j : Fin 3) :
    cellI (fun y => pdR j φ y * ψ y) = -cellI (fun y => φ y * pdR j ψ y) := by
  have h0 := cellI_pdR (h.mul h') j
  rw [pdR_mul (h.1.differentiable (by simp)) (h'.1.differentiable (by simp))] at h0
  rw [cellI_add (φ := fun y => pdR j φ y * ψ y) (ψ := fun y => φ y * pdR j ψ y)
    ((h.pdR j).cont.mul h'.cont) (h.cont.mul (h'.pdR j).cont)] at h0
  linarith

lemma cellI_ibp' {φ ψ : T3 → ℝ} (h : PerR φ) (h' : PerR ψ) (j : Fin 3) :
    cellI (fun y => φ y * pdR j ψ y) = -cellI (fun y => pdR j φ y * ψ y) := by
  rw [cellI_ibp h h' j, neg_neg]

/-- Pointwise two-term domination integrates. -/
lemma cellI_le_two {f p q : T3 → ℝ} (hf : Continuous f) (hp : Continuous p) (hq : Continuous q)
    (c₁ c₂ : ℝ) (hle : ∀ y, f y ≤ c₁ * p y + c₂ * q y) :
    cellI f ≤ c₁ * cellI p + c₂ * cellI q := by
  have := cellI_mono (ψ := fun y => c₁ * p y + c₂ * q y) hf (by fun_prop) hle
  rwa [cellI_add (φ := fun y => c₁ * p y) (ψ := fun y => c₂ * q y) (continuous_const.mul hp)
    (continuous_const.mul hq), cellI_const_mul, cellI_const_mul] at this

/-! ### Gagliardo–Nirenberg -/

/-- **Proved.** Gagliardo–Nirenberg on the unit cell: if `|g| ≤ M` then
`∫ (∂ₐg)⁴ ≤ 9 M² ∫ (∂ₐ∂ₐg)²`. -/
theorem gagliardoNirenberg_cell {g : T3 → ℝ} (hg : PerR g) {M : ℝ} (hM : ∀ y, |g y| ≤ M)
    (a : Fin 3) :
    cellI (fun y => pdR a g y ^ 4) ≤ 9 * M ^ 2 * cellI (fun y => pdR a (pdR a g) y ^ 2) := by
  set w := pdR a g with hw_def
  set z := pdR a w with hz_def
  have hw : PerR w := hg.pdR a
  have hz : PerR z := hw.pdR a
  set ψ : T3 → ℝ := fun y => w y * (w y * w y) with hψ_def
  have hψ : PerR ψ := hw.mul (hw.mul hw)
  have hdw : Differentiable ℝ w := hw.1.differentiable (by simp)
  have hdψ : pdR a ψ = fun y => z y * (w y * w y) + w y * (z y * w y + w y * z y) := by
    simp only [ψ]
    have hww : Differentiable ℝ (fun y => w y * w y) := hdw.mul hdw
    rw [pdR_mul hdw hww, pdR_mul hdw hdw]
  have hibp := cellI_ibp hg hψ a
  rw [hdψ] at hibp
  have hX : cellI (fun y => w y ^ 4) = cellI (fun y => -3 * (g y * (w y ^ 2 * z y))) := by
    have e1 : (fun y => w y ^ 4) = fun y => pdR a g y * ψ y := by
      funext y; simp only [ψ, ← hw_def]; ring
    have e2 : (fun y => -3 * (g y * (w y ^ 2 * z y))) =
        fun y => -(g y * (z y * (w y * w y) + w y * (z y * w y + w y * z y))) := by
      funext y; ring
    rw [e1, hibp, e2, cellI_neg]
  have hle : ∀ y, -3 * (g y * (w y ^ 2 * z y)) ≤ (1 / 2) * w y ^ 4 + (9 * M ^ 2 / 2) * z y ^ 2 :=
    fun y => by
      have h1 : -(g y * z y) ≤ M * |z y| := by
        calc -(g y * z y) ≤ |g y * z y| := neg_le_abs _
          _ = |g y| * |z y| := abs_mul _ _
          _ ≤ M * |z y| := mul_le_mul_of_nonneg_right (hM y) (abs_nonneg _)
      have h2 : 0 ≤ w y ^ 2 := sq_nonneg _
      have h3 : (M * |z y|) ^ 2 = M ^ 2 * z y ^ 2 := by rw [mul_pow, sq_abs]
      nlinarith [sq_nonneg (w y ^ 2 - 3 * (M * |z y|)), mul_le_mul_of_nonneg_left h1 h2]
  have hcont3 : Continuous fun y => -3 * (g y * (w y ^ 2 * z y)) :=
    continuous_const.mul (hg.cont.mul ((hw.cont.pow 2).mul hz.cont))
  have := cellI_le_two hcont3 (hw.cont.pow 4) (hz.cont.pow 2) _ _ hle
  rw [← hX] at this
  · linarith

/-- **Proved.** Mixed Gagliardo–Nirenberg / AM–GM bound:
`∫ (∂ₐg)² |R| ≤ (M/2) (9 ∫ (∂ₐ∂ₐg)² + ∫ R²)` when `|g| ≤ M`. -/
theorem cellI_sq_mul_abs_le {g R : T3 → ℝ} (hg : PerR g) (hR : PerR R) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y, |g y| ≤ M) (a : Fin 3) :
    cellI (fun y => pdR a g y ^ 2 * |R y|) ≤
      M / 2 * (9 * cellI (fun y => pdR a (pdR a g) y ^ 2) + cellI (fun y => R y ^ 2)) := by
  have hP : PerR (pdR a g) := hg.pdR a
  have hGN := gagliardoNirenberg_cell hg hM a
  set X := cellI (fun y => pdR a g y ^ 4)
  set Z := cellI (fun y => pdR a (pdR a g) y ^ 2)
  set S := cellI (fun y => R y ^ 2)
  set Y := cellI (fun y => pdR a g y ^ 2 * |R y|)
  have hS : 0 ≤ S := cellI_nonneg fun y => sq_nonneg _
  have hZ : 0 ≤ Z := cellI_nonneg fun y => sq_nonneg _
  have key : ∀ t : ℝ, 0 < t → Y ≤ 1 / (2 * t) * X + t / 2 * S := fun t ht => by
    refine cellI_le_two ((hP.cont.pow 2).mul hR.cont.abs) (hP.cont.pow 4) (hR.cont.pow 2) _ _
      fun y => ?_
    show pdR a g y ^ 2 * |R y| ≤ _
    have h := sq_nonneg (pdR a g y ^ 2 - t * |R y|)
    have hR2 : |R y| ^ 2 = R y ^ 2 := sq_abs _
    rw [div_mul_eq_mul_div, one_mul, div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
    have e : t / 2 * R y ^ 2 * (2 * t) = t ^ 2 * |R y| ^ 2 := by rw [hR2]; ring
    have h' : (pdR a g y ^ 2 - t * |R y|) ^ 2 =
        pdR a g y ^ 4 - pdR a g y ^ 2 * |R y| * (2 * t) + t ^ 2 * |R y| ^ 2 := by ring
    rw [e]; linarith
  rcases hM0.lt_or_eq with hpos | hzero
  · have h1 := key M hpos
    have h2 : 1 / (2 * M) * X ≤ 1 / (2 * M) * (9 * M ^ 2 * Z) :=
      mul_le_mul_of_nonneg_left hGN (by positivity)
    have h3 : 1 / (2 * M) * (9 * M ^ 2 * Z) = M / 2 * (9 * Z) := by field_simp
    nlinarith
  · subst hzero
    have hX : X ≤ 0 := by simpa using hGN
    simp only [zero_div, zero_mul]
    by_contra hY
    push Not at hY
    have ht : 0 < Y / (S + 1) := div_pos hY (by linarith)
    have h1 := key _ ht
    have h2 : 1 / (2 * (Y / (S + 1))) * X ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hX
    have h3 : Y / (S + 1) / 2 * S < Y := by
      rw [div_div, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
    linarith

lemma bddAbove_norm_fderiv {v : VelocityField} (hv : IsPeriodicSmoothInitialData v) :
    BddAbove (range fun x => ‖fderiv ℝ v x‖) := by
  have hc : Continuous fun x => ‖fderiv ℝ v x‖ := (hv.1.continuous_fderiv (by simp)).norm
  have hK : IsCompact ((fun r : ℝ × ℝ × ℝ => Torus.toT3 r.1 r.2.1 r.2.2) ''
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).image Corrected.continuous_toT3'
  obtain ⟨B, hB⟩ := (hK.image hc).bddAbove
  refine ⟨B, ?_⟩
  rintro _ ⟨x, rfl⟩
  obtain ⟨a, ha, b, hb, c, hc', k, rfl⟩ := Corrected.exists_cell x
  have hper := Corrected.isZ3Periodic_fderiv hv.2.2 (Torus.toT3 a b c) k
  simp only at hper ⊢
  rw [hper]
  exact hB ⟨Torus.toT3 a b c, ⟨(a, b, c), ⟨ha, hb, hc'⟩, rfl⟩, rfl⟩

/-- **Proved.** Each first partial derivative of each velocity component is bounded by
`gradSupNorm`. -/
lemma abs_pdR_coord_le {v : VelocityField} (hv : IsPeriodicSmoothInitialData v) (a l : Fin 3)
    (y : T3) : |pdR a (fun y => v y l) y| ≤ gradSupNorm v := by
  have e : pdR a (fun y => v y l) y = fderiv ℝ v y (EuclideanSpace.single a 1) l :=
    fderiv_coord ((hv.1.differentiable (by simp)) y) l _
  rw [e, ← Real.norm_eq_abs]
  calc ‖fderiv ℝ v y (EuclideanSpace.single a 1) l‖
      ≤ ‖fderiv ℝ v y (EuclideanSpace.single a 1)‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖fderiv ℝ v y‖ * ‖(EuclideanSpace.single a (1 : ℝ) : T3)‖ :=
        (fderiv ℝ v y).le_opNorm _
    _ = ‖fderiv ℝ v y‖ := by simp
    _ ≤ gradSupNorm v := le_ciSup (bddAbove_norm_fderiv hv) y

/-! ### Iterated derivatives along a list of directions -/

/-- Coined. `DL [a₁, …, aₘ] φ = ∂_{a₁} ⋯ ∂_{aₘ} φ`. -/
def DL : List (Fin 3) → (T3 → ℝ) → T3 → ℝ
  | [], φ => φ
  | a :: L, φ => pdR a (DL L φ)

lemma PerR.DL {φ : T3 → ℝ} (h : PerR φ) : ∀ L, PerR (PeriodicNSContinuation.DL L φ)
  | [] => h
  | a :: L => (h.DL L).pdR a

lemma DL_append (L L' : List (Fin 3)) (φ : T3 → ℝ) : DL (L ++ L') φ = DL L (DL L' φ) := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.cons_append, DL, ih]

lemma DL_pdR {φ : T3 → ℝ} (h : PerR φ) (l : Fin 3) :
    ∀ L, DL L (pdR l φ) = pdR l (DL L φ)
  | [] => rfl
  | a :: L => by simp only [DL, DL_pdR h l L]; exact pdR_comm (h.DL L).1 a l

/-- `pdR` of a finite list sum of fields. -/
lemma pdR_listSum {α : Type*} (l : List α) {F : α → T3 → ℝ} (h : ∀ p, Differentiable ℝ (F p))
    (j : Fin 3) : pdR j (fun y => (l.map fun p => F p y).sum) =
      fun y => (l.map fun p => pdR j (F p) y).sum := by
  induction l with
  | nil => funext y; simp [pdR]
  | cons p l ih =>
    have hd : Differentiable ℝ (fun y => (l.map fun p => F p y).sum) := by
      clear ih; induction l with
      | nil => simp
      | cons q l ih' => simpa using (h q).add ih'
    simp only [List.map_cons, List.sum_cons]
    rw [pdR_add (h p) hd, ih]

/-- Coined. All ways to split a list of directions between two factors (Leibniz). -/
def splits : List (Fin 3) → List (List (Fin 3) × List (Fin 3))
  | [] => [([], [])]
  | a :: L => (splits L).map (fun p => (p.1, a :: p.2)) ++ (splits L).map (fun p => (a :: p.1, p.2))

lemma splits_length : ∀ L : List (Fin 3), (splits L).length = 2 ^ L.length
  | [] => rfl
  | a :: L => by simp [splits, splits_length L, pow_succ]; ring

lemma mem_splits : ∀ (L : List (Fin 3)) (p), p ∈ splits L → p.1.length + p.2.length = L.length
  | [], p, hp => by simp [splits] at hp; subst hp; rfl
  | a :: L, p, hp => by
    simp only [splits, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩ <;>
      simp only [List.length_cons] <;> have := mem_splits L q hq <;> omega

lemma splits_eq : ∀ L : List (Fin 3), ∃ T, splits L = ([], L) :: T ∧ ∀ p ∈ T, p.1 ≠ []
  | [] => ⟨[], rfl, by simp⟩
  | a :: L => by
    obtain ⟨T, hT, hT'⟩ := splits_eq L
    refine ⟨T.map (fun p => (p.1, a :: p.2)) ++ (splits L).map (fun p => (a :: p.1, p.2)),
      by simp [splits, hT], fun p hp => ?_⟩
    simp only [List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact hT' q hq
    · simp

/-- **Proved.** General Leibniz rule along a list of directions. -/
lemma DL_mul {f g : T3 → ℝ} (hf : PerR f) (hg : PerR g) : ∀ L : List (Fin 3),
    DL L (fun y => f y * g y) = fun y => ((splits L).map fun p => DL p.1 f y * DL p.2 g y).sum
  | [] => by funext y; simp [DL, splits]
  | a :: L => by
    simp only [DL]
    rw [DL_mul hf hg L, pdR_listSum (splits L)
      (F := fun (p : List (Fin 3) × List (Fin 3)) y => DL p.1 f y * DL p.2 g y)
      (fun p => ((hf.DL p.1).mul (hg.DL p.2)).1.differentiable (by simp)) a]
    funext y
    have e : ∀ p : List (Fin 3) × List (Fin 3), pdR a (fun y => DL p.1 f y * DL p.2 g y) y =
        DL p.1 f y * DL (a :: p.2) g y + DL (a :: p.1) f y * DL p.2 g y := fun p => by
      rw [pdR_mul ((hf.DL p.1).1.differentiable (by simp)) ((hg.DL p.2).1.differentiable (by simp))]
      simp only [DL]; ring
    simp only [e, splits, List.map_append, List.map_map, List.sum_append, Function.comp_def]
    exact List.sum_map_add

lemma DL_sum {ι : Type*} (s : Finset ι) {F : ι → T3 → ℝ} (h : ∀ i, PerR (F i)) :
    ∀ L, DL L (fun y => ∑ i ∈ s, F i y) = fun y => ∑ i ∈ s, DL L (F i) y
  | [] => rfl
  | a :: L => by
    simp only [DL]; rw [DL_sum s h L, pdR_sum s fun i => ((h i).DL L).1.differentiable (by simp)]

/-! ### The `H³`-type quantity on physical side -/

/-- Coined. The direction list read off a word of length three in `Option (Fin 3)`. -/
def toL (w : Fin 3 → Option (Fin 3)) : List (Fin 3) := (List.ofFn w).filterMap id

lemma exists_toL (L : List (Fin 3)) (hL : L.length ≤ 3) : ∃ w, toL w = L := by
  refine ⟨fun j => L[(j : ℕ)]?, ?_⟩
  rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, L⟩⟩⟩⟩ <;> simp_all [toL, List.ofFn_succ] <;> omega

lemma toL_length (w : Fin 3 → Option (Fin 3)) : (toL w).length ≤ 3 := by
  unfold toL
  exact (List.length_filterMap_le _ _).trans (by simp)

/-- Coined. `∑ᵢ ∑_{words} ∫ (D_w vᵢ)²`, a physical-space `H³`-type quantity. -/
def physQ (v : VelocityField) : ℝ :=
  ∑ i, ∑ w : Fin 3 → Option (Fin 3), cellI (fun y => DL (toL w) (fun y => v y i) y ^ 2)

lemma le_physQ (v : VelocityField) (i : Fin 3) (L : List (Fin 3)) (hL : L.length ≤ 3) :
    cellI (fun y => DL L (fun y => v y i) y ^ 2) ≤ physQ v := by
  obtain ⟨w, rfl⟩ := exists_toL L hL
  have hnn : ∀ i w, 0 ≤ cellI (fun y => DL (toL w) (fun y => v y i) y ^ 2) := fun _ _ =>
    cellI_nonneg fun _ => sq_nonneg _
  calc _ ≤ ∑ w : Fin 3 → Option (Fin 3), cellI (fun y => DL (toL w) (fun y => v y i) y ^ 2) :=
        Finset.single_le_sum (f := fun w => cellI (fun y => DL (toL w) (fun y => v y i) y ^ 2))
          (fun w _ => hnn i w) (Finset.mem_univ w)
    _ ≤ physQ v := Finset.single_le_sum (f := fun i => ∑ w : Fin 3 → Option (Fin 3),
          cellI (fun y => DL (toL w) (fun y => v y i) y ^ 2))
          (fun i _ => Finset.sum_nonneg fun w _ => hnn i w) (Finset.mem_univ i)

lemma physQ_nonneg (v : VelocityField) : 0 ≤ physQ v :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => cellI_nonneg fun _ => sq_nonneg _

lemma abs_cellI_le {f : T3 → ℝ} : |cellI f| ≤ cellI (fun y => |f y|) :=
  abs_integral_le_integral_abs

/-- **Proved.** Each lower-order Leibniz term is bounded by `5 ‖∇v‖_∞ Q`. -/
theorem lower_term_bound {v : VelocityField} (hv : IsPeriodicSmoothInitialData v)
    (L : List (Fin 3)) (hL : L.length ≤ 3) (p : List (Fin 3) × List (Fin 3))
    (hp : p.1.length + p.2.length = L.length) (hp1 : p.1 ≠ []) (i l : Fin 3) :
    |cellI (fun y => DL L (fun y => v y i) y *
        (DL p.1 (fun y => v y l) y * DL p.2 (pdR l (fun y => v y i)) y))| ≤
      5 * gradSupNorm v * physQ v := by
  set M := gradSupNorm v
  have hM0 : 0 ≤ M := gradSupNorm_nonneg v
  have hφ : ∀ l, PerR (fun y => v y l) := fun l => perR_coord hv.1 hv.2.2 l
  have hgrad : ∀ a l y, |pdR a (fun y => v y l) y| ≤ M := abs_pdR_coord_le hv
  set R := DL L (fun y => v y i)
  have hR : PerR R := (hφ i).DL L
  have hQ := physQ_nonneg v
  have hRQ : cellI (fun y => R y ^ 2) ≤ physQ v := le_physQ v i L hL
  refine abs_cellI_le.trans ?_
  obtain ⟨A, B⟩ := p
  simp only at hp hp1 ⊢
  rcases A with _ | ⟨a, A'⟩
  · exact absurd rfl hp1
  rcases A' with _ | ⟨b, A''⟩
  · -- one derivative on the transporting field
    have hB : PerR (DL B (pdR l (fun y => v y i))) := ((hφ i).pdR l).DL B
    have hBQ : cellI (fun y => DL B (pdR l (fun y => v y i)) y ^ 2) ≤ physQ v := by
      have := le_physQ v i (B ++ [l]) (by simp at hp ⊢; omega)
      rwa [DL_append] at this
    have := cellI_le_two (f := fun y => |R y * (DL [a] (fun y => v y l) y *
        DL B (pdR l (fun y => v y i)) y)|) (p := fun y => R y ^ 2)
      (q := fun y => DL B (pdR l (fun y => v y i)) y ^ 2)
      (hR.cont.mul ((((hφ l).DL [a]).cont).mul hB.cont)).abs (hR.cont.pow 2)
      (hB.cont.pow 2) (M / 2) (M / 2) fun y => by
        have h1 := hgrad a l y
        simp only [DL] at h1 ⊢
        rw [abs_mul, abs_mul]
        have h2 : |R y| * |DL B (pdR l (fun y => v y i)) y| ≤
            (R y ^ 2 + DL B (pdR l (fun y => v y i)) y ^ 2) / 2 := by
          nlinarith [sq_nonneg (|R y| - |DL B (pdR l (fun y => v y i)) y|), sq_abs (R y),
            sq_abs (DL B (pdR l (fun y => v y i)) y)]
        calc |R y| * (|pdR a (fun y => v y l) y| * |DL B (pdR l (fun y => v y i)) y|)
            ≤ |R y| * (M * |DL B (pdR l (fun y => v y i)) y|) := by gcongr
          _ = M * (|R y| * |DL B (pdR l (fun y => v y i)) y|) := by ring
          _ ≤ M * ((R y ^ 2 + DL B (pdR l (fun y => v y i)) y ^ 2) / 2) := by gcongr
          _ = _ := by ring
    nlinarith
  rcases B with _ | ⟨c, B'⟩
  · -- no derivative on the transported gradient
    set A := DL (a :: b :: A'') (fun y => v y l)
    have hA : PerR A := (hφ l).DL _
    have hAQ : cellI (fun y => A y ^ 2) ≤ physQ v := le_physQ v l _ (by simp at hp ⊢; omega)
    have := cellI_le_two (f := fun y => |R y * (A y * DL [] (pdR l (fun y => v y i)) y)|)
      (p := fun y => R y ^ 2) (q := fun y => A y ^ 2)
      (hR.cont.mul (hA.cont.mul ((hφ i).pdR l).cont)).abs (hR.cont.pow 2)
      (hA.cont.pow 2) (M / 2) (M / 2) fun y => by
        have h1 := hgrad l i y
        simp only [DL] at h1 ⊢
        rw [abs_mul, abs_mul]
        have h2 : |R y| * |A y| ≤ (R y ^ 2 + A y ^ 2) / 2 := by
          nlinarith [sq_nonneg (|R y| - |A y|), sq_abs (R y), sq_abs (A y)]
        calc |R y| * (|A y| * |pdR l (fun y => v y i) y|) ≤ |R y| * (|A y| * M) := by gcongr
          _ = M * (|R y| * |A y|) := by ring
          _ ≤ M * ((R y ^ 2 + A y ^ 2) / 2) := by gcongr
          _ = _ := by ring
    nlinarith
  · -- the Gagliardo–Nirenberg case
    have hA'' : A'' = [] := by
      rcases A'' with _ | ⟨d, _⟩
      · rfl
      · simp at hp; omega
    have hB' : B' = [] := by
      rcases B' with _ | ⟨d, _⟩
      · rfl
      · simp at hp; omega
    subst hA'' hB'
    set g := pdR b (fun y => v y l)
    set g' := pdR l (fun y => v y i)
    have hg : PerR g := (hφ l).pdR b
    have hg' : PerR g' := (hφ i).pdR l
    have h1 := cellI_sq_mul_abs_le hg hR hM0 (hgrad b l) a
    have h2 := cellI_sq_mul_abs_le hg' hR hM0 (hgrad l i) c
    have hZ1 : cellI (fun y => pdR a (pdR a g) y ^ 2) ≤ physQ v :=
      le_physQ v l [a, a, b] (by simp)
    have hZ2 : cellI (fun y => pdR c (pdR c g') y ^ 2) ≤ physQ v :=
      le_physQ v i [c, c, l] (by simp)
    have := cellI_le_two (f := fun y => |R y * (DL [a, b] (fun y => v y l) y *
        DL [c] (pdR l (fun y => v y i)) y)|) (p := fun y => pdR a g y ^ 2 * |R y|)
      (q := fun y => pdR c g' y ^ 2 * |R y|)
      (hR.cont.mul ((hg.pdR a).cont.mul (hg'.pdR c).cont)).abs
      (((hg.pdR a).cont.pow 2).mul hR.cont.abs) (((hg'.pdR c).cont.pow 2).mul hR.cont.abs)
      (1 / 2) (1 / 2) fun y => by
        simp only [DL]
        rw [abs_mul, abs_mul]
        nlinarith [sq_nonneg (|pdR a g y| - |pdR c g' y|), sq_abs (pdR a g y),
          sq_abs (pdR c g' y), abs_nonneg (R y)]
    simp only [DL] at this ⊢
    nlinarith

/-- **Proved.** The top-order Leibniz term vanishes because `div v = 0`. -/
theorem top_term_zero {v : VelocityField} (hv : IsPeriodicSmoothInitialData v)
    (L : List (Fin 3)) :
    ∑ i, ∑ l, cellI (fun y => DL L (fun y => v y i) y *
        (DL [] (fun y => v y l) y * DL L (pdR l (fun y => v y i)) y)) = 0 := by
  have hφ : ∀ l, PerR (fun y => v y l) := fun l => perR_coord hv.1 hv.2.2 l
  set R : Fin 3 → T3 → ℝ := fun i => DL L (fun y => v y i)
  have hR : ∀ i, PerR (R i) := fun i => (hφ i).DL L
  set F : T3 → ℝ := fun y => ∑ i, R i y * R i y
  have hF : PerR F := PerR.sum _ fun i => (hR i).mul (hR i)
  have hdF : ∀ l, pdR l F = fun y => ∑ i, 2 * (R i y * pdR l (R i) y) := fun l => by
    simp only [F]
    rw [pdR_sum _ fun i => ((hR i).mul (hR i)).1.differentiable (by simp)]
    funext y
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pdR_mul ((hR i).1.differentiable (by simp)) ((hR i).1.differentiable (by simp))]; ring
  have e : ∀ i l, (fun y => DL L (fun y => v y i) y *
      (DL [] (fun y => v y l) y * DL L (pdR l (fun y => v y i)) y)) =
      fun y => v y l * (R i y * pdR l (R i) y) := fun i l => by
    funext y; simp only [DL, R, DL_pdR (hφ i) l L]; ring
  simp only [e]
  rw [Finset.sum_comm]
  have hc : ∀ i l, Continuous fun y => v y l * (R i y * pdR l (R i) y) := fun i l =>
    (hφ l).cont.mul ((hR i).cont.mul ((hR i).pdR l).cont)
  have step : ∀ l, ∑ i, cellI (fun y => v y l * (R i y * pdR l (R i) y)) =
      -(1 / 2) * cellI (fun y => pdR l (fun y => v y l) y * F y) := fun l => by
    rw [← cellI_sum _ fun i => hc i l]
    have h1 : (fun y => ∑ i, v y l * (R i y * pdR l (R i) y)) =
        fun y => (1 / 2) * (v y l * pdR l F y) := by
      funext y; rw [hdF]; simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [h1, cellI_const_mul, cellI_ibp' (hφ l) hF l]; ring
  simp only [step, ← Finset.mul_sum]
  rw [← cellI_sum (φ := fun l y => pdR l (fun y => v y l) y * F y) _
    fun l => ((hφ l).pdR l).cont.mul hF.cont]
  have h0 : (fun y => ∑ l, pdR l (fun y => v y l) y * F y) = fun _ => 0 := by
    funext y; rw [← Finset.sum_mul]
    have := hv.2.1 y
    simp only [div] at this
    simp only [pdR, this, zero_mul]
  rw [h0]; simp [cellI]

end PeriodicNSContinuation
