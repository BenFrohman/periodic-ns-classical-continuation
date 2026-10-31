/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import PeriodicNSContinuation.FourierInversion

/-!
# Parseval's identity for `cubeCoeff`

**Proved:** `hasSum_prod_cubeCoeff` — for continuous `ℤ³`-periodic `f g : ℝ³ → ℂ`,
`Σ_k conj(f̂_k) ĝ_k = ∫_{[0,1]³} conj(f) g`. Transferred from Mathlib's
`hasSum_prod_mFourierCoeff` on `UnitAddTorus (Fin 3)`.
-/

noncomputable section
open Set Filter Topology MeasureTheory FeffermanClayNS NavierStokes3D UnitAddTorus

namespace PeriodicNSContinuation

noncomputable local instance parsevalMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance parsevalProb : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Descent of a `ℤ³`-periodic function to the torus (coined). -/
def torusLift (g : (Fin 3 → ℝ) → ℂ) : UnitAddTorus (Fin 3) → ℂ :=
  fun z => g (Function.surjInv isOpenQuotientMap_torusMk.surjective z)

lemma torusLift_mk {g : (Fin 3 → ℝ) → ℂ} (hg : ∀ y (n : Fin 3 → ℤ), g (y + fun j => (n j : ℝ)) = g y)
    (y : Fin 3 → ℝ) : torusLift g (torusMk y) = g y := by
  unfold torusLift
  obtain ⟨n, hn⟩ := torusMk_eq
    (Function.surjInv_eq isOpenQuotientMap_torusMk.surjective (torusMk y))
  conv_rhs => rw [hn]
  exact (hg _ n).symm

lemma continuous_torusLift {g : (Fin 3 → ℝ) → ℂ} (hc : Continuous g)
    (hg : ∀ y (n : Fin 3 → ℤ), g (y + fun j => (n j : ℝ)) = g y) : Continuous (torusLift g) := by
  refine isOpenQuotientMap_torusMk.isQuotientMap.continuous_iff.2 ?_
  have : torusLift g ∘ torusMk = g := funext (torusLift_mk hg)
  rw [this]; exact hc

lemma integral_torusLift {F : UnitAddTorus (Fin 3) → ℂ} {G : (Fin 3 → ℝ) → ℂ}
    (h : ∀ y, F (torusMk y) = G y) :
    ∫ z, F z = ∫ x in Icc (0 : Fin 3 → ℝ) 1, G x := by
  rw [integral_preimage F 0]
  have hset : {x : Fin 3 → ℝ | ∀ j, x j ∈ Ioc ((0 : Fin 3 → ℝ) j) ((0 : Fin 3 → ℝ) j + 1)} =
      univ.pi fun _ => Ioc (0 : ℝ) 1 := by ext x; simp
  have hae : (univ.pi fun _ => Ioc (0 : ℝ) 1) =ᵐ[(volume : Measure (Fin 3 → ℝ))]
      Icc (0 : Fin 3 → ℝ) 1 := by
    rw [volume_pi]
    exact Measure.univ_pi_Ioc_ae_eq_Icc (f := fun _ => (0 : ℝ)) (g := fun _ => (1 : ℝ))
  rw [hset, setIntegral_congr_set hae]
  exact setIntegral_congr_fun measurableSet_Icc fun x _ => h x

lemma mFourierCoeff_torusLift {g : (Fin 3 → ℝ) → ℂ}
    (hg : ∀ y (n : Fin 3 → ℤ), g (y + fun j => (n j : ℝ)) = g y) (k : Fin 3 → ℤ) :
    mFourierCoeff (torusLift g) k = cubeCoeff g k := by
  unfold mFourierCoeff cubeCoeff
  refine integral_torusLift fun y => ?_
  rw [torusLift_mk hg, smul_eq_mul, mul_comm, mFourier_torusMk]
  congr 2
  simp only [Pi.neg_apply, Int.cast_neg, Complex.ofReal_neg, neg_mul, Finset.sum_neg_distrib]
  ring

/-- **Parseval's identity** (proved) for continuous `ℤ³`-periodic functions, in `cubeCoeff` form. -/
theorem hasSum_prod_cubeCoeff {f g : (Fin 3 → ℝ) → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfp : ∀ y (n : Fin 3 → ℤ), f (y + fun j => (n j : ℝ)) = f y)
    (hgp : ∀ y (n : Fin 3 → ℤ), g (y + fun j => (n j : ℝ)) = g y) :
    HasSum (fun k => (starRingEnd ℂ) (cubeCoeff f k) * cubeCoeff g k)
      (∫ x in Icc (0 : Fin 3 → ℝ) 1, (starRingEnd ℂ) (f x) * g x) := by
  set F : C(UnitAddTorus (Fin 3), ℂ) := ⟨torusLift f, continuous_torusLift hf hfp⟩
  set G : C(UnitAddTorus (Fin 3), ℂ) := ⟨torusLift g, continuous_torusLift hg hgp⟩
  have h := hasSum_prod_mFourierCoeff (F.toLp 2 (MeasureTheory.volume : Measure (UnitAddTorus (Fin 3))) ℂ) (G.toLp 2 (MeasureTheory.volume : Measure (UnitAddTorus (Fin 3))) ℂ)
  simp only [mFourierCoeff_toLp] at h
  have hF : ∀ k, mFourierCoeff F k = cubeCoeff f k := mFourierCoeff_torusLift hfp
  have hG : ∀ k, mFourierCoeff G k = cubeCoeff g k := mFourierCoeff_torusLift hgp
  simp only [hF, hG] at h
  convert h using 1
  have hae : (fun t => (starRingEnd ℂ) ((F.toLp 2 (MeasureTheory.volume :
      Measure (UnitAddTorus (Fin 3))) ℂ) t) * (G.toLp 2 (MeasureTheory.volume :
      Measure (UnitAddTorus (Fin 3))) ℂ) t) =ᵐ[MeasureTheory.volume]
      fun t => (starRingEnd ℂ) (F t) * G t := by
    filter_upwards [F.coeFn_toLp (p := 2) (μ := (MeasureTheory.volume :
      Measure (UnitAddTorus (Fin 3)))) (𝕜 := ℂ), G.coeFn_toLp (p := 2) (μ := (MeasureTheory.volume :
      Measure (UnitAddTorus (Fin 3)))) (𝕜 := ℂ)] with t h1 h2
    rw [h1, h2]
  rw [integral_congr_ae hae]
  symm
  refine integral_torusLift fun y => ?_
  simp [F, G, torusLift_mk hfp, torusLift_mk hgp]

end PeriodicNSContinuation
