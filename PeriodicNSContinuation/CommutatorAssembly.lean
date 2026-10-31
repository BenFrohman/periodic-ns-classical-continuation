/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.KatoPonce

/-!
# Discharging the `s = 3` physical-space commutator bound

Expands `∫ (1 - Δ/4π²)³ φ · χ` over derivative words (`wordSum`), bounds each word by the
Kato–Ponce estimates of `KatoPonce.lean`, and compares `physQ` with `hsSq 3`.
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D TorusFourierNS
open scoped ContDiff

namespace PeriodicNSContinuation

lemma pdR_helmR {ψ : T3 → ℝ} (h : PerR ψ) (j : Fin 3) : pdR j (helmR ψ) = helmR (pdR j ψ) := by
  have e : helmR ψ = fun y => ψ y + (-(4 * Real.pi ^ 2)⁻¹) * ∑ m, pdR m (pdR m ψ) y := by
    funext y; simp only [helmR]; ring
  have hd : ∀ m, Differentiable ℝ (pdR m (pdR m ψ)) := fun m =>
    ((h.pdR m).pdR m).1.differentiable (by simp)
  have hs : Differentiable ℝ (fun y => ∑ m, pdR m (pdR m ψ) y) :=
    (ContDiff.sum fun m _ => ((h.pdR m).pdR m).1).differentiable (by simp)
  rw [e, pdR_add (h.1.differentiable (by simp)) (hs.const_mul _) j, pdR_const_mul hs,
    pdR_sum _ hd]
  funext y; simp only [helmR]
  have : ∀ m, pdR j (pdR m (pdR m ψ)) = pdR m (pdR m (pdR j ψ)) := fun m => by
    rw [pdR_comm (h.pdR m).1 j m, pdR_comm h.1 j m]
  simp only [this]; ring

lemma DL_helmR {ψ : T3 → ℝ} (h : PerR ψ) : ∀ L, DL L (helmR ψ) = helmR (DL L ψ)
  | [] => rfl
  | a :: L => by simp only [DL, DL_helmR h L]; exact pdR_helmR (h.DL L) a

lemma cellI_helmR_mul {A B : T3 → ℝ} (hA : PerR A) (hB : PerR B) :
    cellI (fun y => helmR A y * B y) = cellI (fun y => A y * B y) +
      (4 * Real.pi ^ 2)⁻¹ * ∑ j, cellI (fun y => pdR j A y * pdR j B y) := by
  have e : (fun y => helmR A y * B y) = fun y => A y * B y +
      (-(4 * Real.pi ^ 2)⁻¹) * ∑ j, pdR j (pdR j A) y * B y := by
    funext y; simp only [helmR]; rw [← Finset.sum_mul]; ring
  have hc : ∀ j, Continuous fun y => pdR j (pdR j A) y * B y := fun j =>
    ((hA.pdR j).pdR j).cont.mul hB.cont
  rw [e, cellI_add (φ := fun y => A y * B y)
    (ψ := fun y => -(4 * Real.pi ^ 2)⁻¹ * ∑ j, pdR j (pdR j A) y * B y) (hA.cont.mul hB.cont)
    (continuous_const.mul (continuous_finset_sum _ fun j _ => hc j)),
    cellI_const_mul, cellI_sum _ hc]
  simp only [fun j => cellI_ibp (hA.pdR j) hB j, Finset.sum_neg_distrib]; ring

/-- Coined. Recursive expansion of `(1 - Δ/4π²)ⁿ` over derivative words prefixed to `L`. -/
def wordSum : ℕ → (List (Fin 3) → ℝ) → List (Fin 3) → ℝ
  | 0, F, L => F L
  | n + 1, F, L => wordSum n F L + (4 * Real.pi ^ 2)⁻¹ * ∑ j, wordSum n F (j :: L)

theorem cellI_iterate_helmR {φ χ : T3 → ℝ} (hφ : PerR φ) (hχ : PerR χ) (n : ℕ) :
    ∀ L, cellI (fun y => DL L (helmR^[n] φ) y * DL L χ y) =
      wordSum n (fun L => cellI (fun y => DL L φ y * DL L χ y)) L := by
  induction n with
  | zero => intro L; rfl
  | succ n ih =>
    intro L
    rw [Function.iterate_succ_apply', DL_helmR (hφ.iterate_helmR n),
      cellI_helmR_mul ((hφ.iterate_helmR n).DL L) (hχ.DL L), wordSum, ← ih L]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← ih (j :: L)]; rfl

lemma wordSum_sum (F : Fin 3 → List (Fin 3) → ℝ) (n : ℕ) : ∀ L,
    wordSum n (fun L => ∑ i, F i L) L = ∑ i, wordSum n (F i) L := by
  induction n with
  | zero => intro L; rfl
  | succ n ih =>
    intro L
    simp only [wordSum, ih, Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm (f := fun x y => (4 * Real.pi ^ 2)⁻¹ * wordSum n (F y) (x :: L))]

lemma helm_const_le_one : (4 * Real.pi ^ 2)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (by nlinarith [Real.pi_gt_three])

lemma helm_const_pos : 0 < (4 * Real.pi ^ 2)⁻¹ := by positivity

theorem abs_wordSum_le {F : List (Fin 3) → ℝ} {K : ℝ} (n : ℕ) : ∀ L,
    (∀ L', L'.length ≤ L.length + n → |F L'| ≤ K) → |wordSum n F L| ≤ 4 ^ n * K := by
  induction n with
  | zero => intro L h; simpa [wordSum] using h L (by simp)
  | succ n ih =>
    intro L h
    have hK : 0 ≤ K := (abs_nonneg _).trans (h L (by omega))
    have h1 := ih L fun L' hL' => h L' (by omega)
    have h2 : ∀ j, |wordSum n F (j :: L)| ≤ 4 ^ n * K := fun j =>
      ih (j :: L) fun L' hL' => h L' (by simp at hL'; omega)
    have h3 : |∑ j, wordSum n F (j :: L)| ≤ 3 * (4 ^ n * K) :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        ((Finset.sum_le_sum fun j _ => h2 j).trans (by simp))
    have hc := helm_const_le_one
    have hc0 := helm_const_pos
    simp only [wordSum]
    calc _ ≤ |wordSum n F L| + (4 * Real.pi ^ 2)⁻¹ * |∑ j, wordSum n F (j :: L)| := by
          exact (abs_add_le _ _).trans (le_of_eq (by rw [abs_mul, abs_of_pos hc0]))
      _ ≤ 4 ^ n * K + 1 * (3 * (4 ^ n * K)) := by
          have := mul_le_mul hc h3 (abs_nonneg _) (by norm_num)
          linarith
      _ = _ := by ring

lemma wordSum_nonneg {F : List (Fin 3) → ℝ} (hF : ∀ L, 0 ≤ F L) (n : ℕ) :
    ∀ L, 0 ≤ wordSum n F L := by
  induction n with
  | zero => exact hF
  | succ n ih =>
    intro L
    exact add_nonneg (ih L) (mul_nonneg helm_const_pos.le (Finset.sum_nonneg fun j _ => ih _))

theorem le_wordSum {F : List (Fin 3) → ℝ} (hF : ∀ L, 0 ≤ F L) (n : ℕ) :
    ∀ L M, M.length ≤ n → (4 * Real.pi ^ 2)⁻¹ ^ n * F (M ++ L) ≤ wordSum n F L := by
  have hc := helm_const_le_one
  have hc0 := helm_const_pos
  induction n with
  | zero => intro L M hM; simp_all [wordSum]
  | succ n ih =>
    intro L M hM
    have hS := wordSum_nonneg hF n
    rcases List.eq_nil_or_concat M with rfl | ⟨M', j, rfl⟩
    · have := ih L [] (by simp)
      have hp : (4 * Real.pi ^ 2)⁻¹ ^ (n + 1) ≤ (4 * Real.pi ^ 2)⁻¹ ^ n :=
        pow_le_pow_of_le_one hc0.le hc (by omega)
      simp only [wordSum, List.nil_append] at this ⊢
      have := mul_le_mul_of_nonneg_right hp (hF L)
      nlinarith [mul_nonneg hc0.le (Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hS (j :: L))]
    · simp at hM
      have h1 := ih (j :: L) M' (by omega)
      have h2 : wordSum n F (j :: L) ≤ ∑ j, wordSum n F (j :: L) :=
        Finset.single_le_sum (f := fun j => wordSum n F (j :: L)) (fun j _ => hS _)
          (Finset.mem_univ j)
      rw [List.concat_eq_append, List.append_assoc, List.singleton_append, pow_succ]
      simp only [wordSum]
      nlinarith [hS L, mul_le_mul_of_nonneg_left (h1.trans h2) hc0.le]

lemma cellI_listSum {α : Type*} (l : List α) {F : α → T3 → ℝ} (h : ∀ p, Continuous (F p)) :
    cellI (fun y => (l.map fun p => F p y).sum) = (l.map fun p => cellI (F p)).sum := by
  induction l with
  | nil => simp [cellI]
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [cellI_add (φ := F a) (ψ := fun y => (l.map fun p => F p y).sum) (h a)
      (continuous_list_sum _ fun p _ => h p), ih]

lemma abs_listSum_le {α : Type*} (l : List α) (f : α → ℝ) {B : ℝ} (h : ∀ p ∈ l, |f p| ≤ B) :
    |(l.map f).sum| ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
    have h1 := h a (by simp)
    have h2 := ih fun p hp => h p (by simp [hp])
    calc _ ≤ |f a| + |(l.map f).sum| := abs_add_le _ _
      _ ≤ _ := by linarith

/-- **Proved.** Per-word commutator estimate: for every derivative word `L` of length `≤ 3`,
`|∑ᵢ ∫ ∂^L vᵢ · ∂^L ((v·∇)v)ᵢ| ≤ 315 ‖∇v‖_∞ physQ v`. -/
theorem word_bound {v : VelocityField} (hv : IsPeriodicSmoothInitialData v)
    (L : List (Fin 3)) (hL : L.length ≤ 3) :
    |∑ i, cellI (fun y => DL L (fun y => v y i) y * DL L (convR v i) y)| ≤
      315 * gradSupNorm v * physQ v := by
  have hφ : ∀ l, PerR (fun y => v y l) := fun l => perR_coord hv.1 hv.2.2 l
  obtain ⟨T, hT, hT1⟩ := splits_eq L
  have hTl : T.length ≤ 7 := by
    have := splits_length L
    rw [hT, List.length_cons] at this
    have : 2 ^ L.length ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hL
    omega
  set R : Fin 3 → T3 → ℝ := fun i => DL L (fun y => v y i)
  have hR : ∀ i, PerR (R i) := fun i => (hφ i).DL L
  set G : Fin 3 → Fin 3 → List (Fin 3) × List (Fin 3) → T3 → ℝ := fun i l p y =>
    R i y * (DL p.1 (fun y => v y l) y * DL p.2 (pdR l (fun y => v y i)) y)
  have hG : ∀ i l p, Continuous (G i l p) := fun i l p =>
    (hR i).cont.mul (((hφ l).DL p.1).cont.mul ((((hφ i).pdR l).DL p.2).cont))
  have hconv : ∀ i, convR v i = fun y => ∑ l ∈ Finset.univ,
      (fun y => v y l * pdR l (fun y => v y i) y) y := fun i => rfl
  have hsplit : ∀ i, cellI (fun y => R i y * DL L (convR v i) y) =
      ∑ l, (cellI (G i l ([], L)) + (T.map fun p => cellI (G i l p)).sum) := fun i => by
    have e : (fun y => R i y * DL L (convR v i) y) =
        fun y => ∑ l, (G i l ([], L) y + (T.map fun p => G i l p y).sum) := by
      funext y
      rw [hconv, DL_sum _ (fun l => (hφ l).mul ((hφ i).pdR l)) L]
      simp only [DL_mul (hφ _) ((hφ i).pdR _) L, hT, List.map_cons, List.sum_cons,
        Finset.mul_sum, mul_add, G]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← List.sum_map_mul_left]
    rw [e, cellI_sum (φ := fun l y => G i l ([], L) y + (T.map fun p => G i l p y).sum) _ fun l => (hG i l _).add (continuous_list_sum _ fun p _ => hG i l p)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [cellI_add (φ := G i l ([], L)) (ψ := fun y => (T.map fun p => G i l p y).sum) (hG i l _)
      (continuous_list_sum _ fun p _ => hG i l p), cellI_listSum _ (hG i l)]
  have htop := top_term_zero hv L
  have hsplit' : ∀ i, cellI (fun y => DL L (fun y => v y i) y * DL L (convR v i) y) =
      ∑ l, (cellI (G i l ([], L)) + (T.map fun p => cellI (G i l p)).sum) := hsplit
  simp only [hsplit', Finset.sum_add_distrib]
  rw [show (∑ i, ∑ l, cellI (G i l ([], L))) = 0 from htop, zero_add]
  have hM := gradSupNorm_nonneg v
  have hQ := physQ_nonneg v
  have hb : ∀ i l, |(T.map fun p => cellI (G i l p)).sum| ≤ 7 * (5 * gradSupNorm v * physQ v) :=
    fun i l => (abs_listSum_le _ _ fun p hp => lower_term_bound hv L hL p
      (mem_splits L p (by rw [hT]; exact List.mem_cons_of_mem _ hp)) (hT1 p hp) i l).trans
      (by gcongr; exact_mod_cast hTl)
  calc _ ≤ ∑ i, ∑ l, |(T.map fun p => cellI (G i l p)).sum| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i : Fin 3, ∑ l : Fin 3, 7 * (5 * gradSupNorm v * physQ v) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ => hb i l
    _ = _ := by simp; ring

/-- **Proved.** `∑ᵢ ∫ (1 - Δ/4π²)³vᵢ · vᵢ = ‖v‖²_{H³}` (Parseval). -/
theorem sum_cellI_helm_three {v : VelocityField} (hv : IsPeriodicSmoothInitialData v) :
    ∑ i, cellI (fun y => (helmR^[3] (fun y => v y i)) y * v y i) = hsSq 3 v := by
  have hφ : ∀ i, PerR (fun y => v y i) := fun i => perR_coord hv.1 hv.2.2 i
  have hs : ∀ i, HasSum (fun k => sobW 3 k * ‖fourierCoeffVF v k i‖ ^ 2)
      (cellI (fun y => (helmR^[3] (fun y => v y i)) y * v y i)) := fun i => by
    refine (hasSum_re_cubeCoeff ((hφ i).iterate_helmR 3) (hφ i)).congr_fun fun k => ?_
    rw [cubeCoeff_iterate_helmR (hφ i), map_mul, Complex.conj_ofReal, mul_assoc,
      Complex.conj_mul', fourierCoeffVF_eq_cubeCoeff, compC_eq_liftR,
      show sobW 3 k = (1 + ∑ j, ((k j : ℝ)) ^ 2) ^ 3 by
        rw [sobW, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]]
    norm_cast
  have h := hasSum_mode_fin (g := fun p : Mode × Fin 3 => sobW 3 p.1 *
    ‖fourierCoeffVF v p.1 p.2‖ ^ 2) hs
  rw [hsSq_eq_tsum, h.tsum_eq]

/-- **Proved.** `physQ v ≤ 64 (4π²)³ ‖v‖²_{H³}`. -/
theorem physQ_le_hsSq {v : VelocityField} (hv : IsPeriodicSmoothInitialData v) :
    physQ v ≤ 64 * (4 * Real.pi ^ 2) ^ 3 * hsSq 3 v := by
  have hφ : ∀ i, PerR (fun y => v y i) := fun i => perR_coord hv.1 hv.2.2 i
  set F : Fin 3 → List (Fin 3) → ℝ := fun i L =>
    cellI (fun y => DL L (fun y => v y i) y * DL L (fun y => v y i) y)
  have hF0 : ∀ L, 0 ≤ ∑ i, F i L := fun L =>
    Finset.sum_nonneg fun i _ => cellI_nonneg fun y => mul_self_nonneg _
  have hW : wordSum 3 (fun L => ∑ i, F i L) [] = hsSq 3 v := by
    rw [wordSum_sum, ← sum_cellI_helm_three hv]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (cellI_iterate_helmR (hφ i) (hφ i) 3 []).symm
  have hc0 := helm_const_pos
  have hw : ∀ w : Fin 3 → Option (Fin 3), ∑ i, F i (toL w) ≤ (4 * Real.pi ^ 2) ^ 3 * hsSq 3 v :=
    fun w => by
      have := le_wordSum hF0 3 [] (toL w) (toL_length w)
      rw [List.append_nil, hW, inv_pow] at this
      have hp : 0 < (4 * Real.pi ^ 2) ^ 3 := by positivity
      rwa [inv_mul_le_iff₀ hp] at this
  have e : physQ v = ∑ w : Fin 3 → Option (Fin 3), ∑ i, F i (toL w) := by
    rw [physQ, Finset.sum_comm]; simp only [F, sq]
  rw [e]
  calc _ ≤ ∑ _w : Fin 3 → Option (Fin 3), (4 * Real.pi ^ 2) ^ 3 * hsSq 3 v :=
        Finset.sum_le_sum fun w _ => hw w
    _ = _ := by simp; ring

/-- **Proved.** The physical-space `s = 3` commutator bound holds, with an explicit constant. -/
theorem periodicPhysicalCommutatorBound :
    PeriodicPhysicalCommutatorBound (2 * 64 * 315 * (64 * (4 * Real.pi ^ 2) ^ 3)) := by
  intro v hv
  have hφ : ∀ i, PerR (fun y => v y i) := fun i => perR_coord hv.1 hv.2.2 i
  set E : List (Fin 3) → ℝ := fun L =>
    ∑ i, cellI (fun y => DL L (fun y => v y i) y * DL L (convR v i) y)
  have hP : ∑ i, cellI (fun y => (helmR^[3] (fun y => v y i)) y * convR v i y) =
      wordSum 3 E [] := by
    rw [wordSum_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact cellI_iterate_helmR (hφ i) (perR_convR hv i) 3 []
  have hb := abs_wordSum_le (F := E) (K := 315 * gradSupNorm v * physQ v) 3 []
    fun L' hL' => word_bound hv L' (by simpa using hL')
  have hQ := physQ_le_hsSq hv
  have hM := gradSupNorm_nonneg v
  have hQ0 := physQ_nonneg v
  have key : -2 * ∑ i, cellI (fun y => (helmR^[3] (fun y => v y i)) y * convR v i y) ≤
      2 * 64 * 315 * (64 * (4 * Real.pi ^ 2) ^ 3) * gradSupNorm v * hsSq 3 v := by
    rw [hP]
    have h1 : -2 * wordSum 3 E [] ≤ 2 * (4 ^ 3 * (315 * gradSupNorm v * physQ v)) := by
      have := neg_abs_le (wordSum 3 E [])
      linarith
    have h2 := mul_le_mul_of_nonneg_left hQ (by positivity : (0:ℝ) ≤ 2 * 64 * 315 * gradSupNorm v)
    nlinarith
  exact key

/-- **Proved.** `∃ C ≥ 0` with `PeriodicPhysicalCommutatorBound C`. -/
theorem exists_periodicPhysicalCommutatorBound :
    ∃ C, 0 ≤ C ∧ PeriodicPhysicalCommutatorBound C :=
  ⟨_, by positivity, periodicPhysicalCommutatorBound⟩

/-- **Proved (conditional only on `PeriodicLowFreqVorticityBound`).** -/
theorem periodicBKMHsControl_three_of_lowFreq (ν : ℝ) (hL : PeriodicLowFreqVorticityBound) :
    PeriodicBKMHsControl ν 3 :=
  periodicBKMHsControl_of_physical_lowFreq ν exists_periodicPhysicalCommutatorBound hL

end PeriodicNSContinuation
