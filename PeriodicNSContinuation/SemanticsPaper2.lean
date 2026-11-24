/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import PeriodicNSContinuation.SemanticsPaper
import PeriodicNSContinuation.BKMFinal
import PeriodicNSContinuation.CoeffODE
import PeriodicNSContinuation.HsEnergyIdentity
import PeriodicNSContinuation.PhysicalCommutator
import PeriodicNSContinuation.CommutatorAssembly
import PeriodicNSContinuation.LowFreqAssembly
import PeriodicNSContinuation.KatoPonce
import PeriodicNSContinuation.Continuation

/-!
# Truth Gate: additional lock "paper-statements-2" (see `TRUTH_GATE.md`)

PAPER_PATH: paper/periodic-ns-classical-continuation.tex
PAPER_SHA256: effd6bb926e424b41076cac25c4363a8d1011b48d729811b805f5d2bc764df2d
PAPER_SECTION: Sections "Proved results (no hypothesis Props)" and "Conditional results"

Each claim `X` has `formal_claim_X` (the statement of the repository theorem),
`paper_claim_X` (an independent transcription of the paper sentence, using only Mathlib, the
main lock's paper-side notions `paperSolOn`, `paperTstar`, `paperCurl`, `paperBKMInt`, and the
paper-side notions `pDatum`, `pMaximal`, `pBKMCriterion`, `pStatementB`, `pD`, `pCube` of the
lock "paper-statements"), and `intended_correspondence_X : formal_claim_X ↔ paper_claim_X`.

The new paper-side notions below are written from Mathlib and from the paper's own definitions:
`pFC` (vector Fourier coefficient on the unit cell), `pW` (Sobolev weight `(1+|k|²)^s`), `pHsSq`,
`pHsNorm` (the `H^s` norm), `pLeray` (Leray projection at mode `k`), `pNS` (Fourier
Navier–Stokes field), `pRate` (weighted energy rate), `pPer` (smooth and `ℤ³`-periodic), `pd`
(partial derivative), `pHelm` (`1 - Δ/4π²`), `pConv` (`(v·∇)v`), `pGradSup` (`‖∇v‖_∞`),
`pPhysQ` (`Q(v)`), `pSplits` (Leibniz splittings), `pVP`, `pLowGrad`, `pLowGradSup` (`‖V_R∇v‖_∞`).

Nothing here proves Statement (B), global regularity, or any Clay problem.
-/

namespace TruthGatePaper2

open scoped ContDiff
open FeffermanClayNS NavierStokes3D PeriodicNSContinuation TorusFourierNS TruthGate TruthGatePaper
  MeasureTheory

-- TRUTH-GATE LOCK BEGIN
/-! ### Paper-side notions (Mathlib only) -/

/-- Paper: `û_k = ∫_{[0,1]³} u(x) e^{-2πi k·x} dx` (componentwise), `k·x = Σⱼ kⱼ xⱼ`. -/
noncomputable def pFC (v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (k : Fin 3 → ℤ)
    (i : Fin 3) : ℂ :=
  ∫ x in Set.Icc (0 : Fin 3 → ℝ) 1,
    ((v ((EuclideanSpace.equiv (Fin 3) ℝ).symm x) i : ℝ) : ℂ) *
      Complex.exp (-(2 * Real.pi * Complex.I) * ∑ j : Fin 3, ((k j : ℝ) : ℂ) * (x j : ℂ))

/-- Paper: the Sobolev weight `(1 + |k|²)^s`. -/
noncomputable def pW (s : ℝ) (k : Fin 3 → ℤ) : ℝ := (1 + ∑ j : Fin 3, ((k j : ℝ)) ^ 2) ^ s

/-- Paper: `‖u‖²_{H^s} = Σ_{k,i} (1+|k|²)^s |û_{k,i}|²`. -/
noncomputable def pHsSq (s : ℝ) (v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑' q : (Fin 3 → ℤ) × Fin 3, pW s q.1 * ‖pFC v q.1 q.2‖ ^ 2

/-- Paper: `‖u‖_{H^s}`. -/
noncomputable def pHsNorm (s : ℝ) (v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Real.sqrt (pHsSq s v)

/-- Paper: the Leray projection at mode `k`, `w ↦ w - (k·w/|k|²) k` (`w` at `k = 0`). -/
noncomputable def pLeray (k : Fin 3 → ℤ) (w : Fin 3 → ℂ) : Fin 3 → ℂ := fun i =>
  w i - (∑ j : Fin 3, ((k j : ℝ) : ℂ) * w j) / ((∑ j : Fin 3, ((k j : ℝ)) ^ 2 : ℝ) : ℂ) *
    ((k i : ℝ) : ℂ)

/-- Paper: the projected Fourier Navier–Stokes field
`F_ν(a)_k = -4π²ν|k|² a_k - P_k(2πi Σ_m (a_m·(k-m)) a_{k-m})`. -/
noncomputable def pNS (ν : ℝ) (a : (Fin 3 → ℤ) → Fin 3 → ℂ) (k : Fin 3 → ℤ) (i : Fin 3) : ℂ :=
  -((4 * Real.pi ^ 2 * ν * ∑ j : Fin 3, ((k j : ℝ)) ^ 2 : ℝ) : ℂ) * a k i -
    pLeray k (fun j => 2 * Real.pi * Complex.I * ∑' m : Fin 3 → ℤ,
      (∑ l : Fin 3, a m l * (((k - m) l : ℤ) : ℂ)) * a (k - m) j) i

/-- Paper: the weighted rate `Σ_{k,i} (1+|k|²)^s 2 Re(conj(a_{k,i}) Φ_{k,i})`. -/
noncomputable def pRate (s : ℝ) (Φ a : (Fin 3 → ℤ) → Fin 3 → ℂ) : ℝ :=
  ∑' q : (Fin 3 → ℤ) × Fin 3, pW s q.1 * (2 * ((starRingEnd ℂ) (a q.1 q.2) * Φ q.1 q.2).re)

/-- Paper: `φ` is smooth and `φ(x+n) = φ(x)` for all `n ∈ ℤ³`. -/
def pPer (φ : EuclideanSpace ℝ (Fin 3) → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧
    ∀ (x : EuclideanSpace ℝ (Fin 3)) (n : Fin 3 → ℤ),
      φ (x + ∑ j : Fin 3, (n j : ℝ) • EuclideanSpace.single j (1 : ℝ)) = φ x

/-- Paper: `∂_j φ`. -/
noncomputable def pd (j : Fin 3) (φ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    EuclideanSpace ℝ (Fin 3) → ℝ :=
  fun y => fderiv ℝ φ y (EuclideanSpace.single j 1)

/-- Paper: `(1 - Δ/4π²) φ`, `Δ = Σⱼ ∂ⱼ∂ⱼ`. -/
noncomputable def pHelm (φ : EuclideanSpace ℝ (Fin 3) → ℝ) : EuclideanSpace ℝ (Fin 3) → ℝ :=
  fun y => φ y - (4 * Real.pi ^ 2)⁻¹ * ∑ j : Fin 3, pd j (pd j φ) y

/-- Paper: `((v·∇)v)_i = Σ_l v_l ∂_l v_i`. -/
noncomputable def pConv (v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (i : Fin 3) :
    EuclideanSpace ℝ (Fin 3) → ℝ :=
  fun y => ∑ l : Fin 3, v y l * pd l (fun z => v z i) y

/-- Paper: `‖∇v‖_{L^∞} = sup_x ‖Dv(x)‖` (operator norm; the real supremum). -/
noncomputable def pGradSup (v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ⨆ x, ‖fderiv ℝ v x‖

/-- Paper: `Q(v) = Σ_i Σ_{w ∈ {∅,1,2,3}³} ∫_{[0,1]³} |D^{w} v_i|²`, where `D^{w}` differentiates
along the entries of `w` that are not `∅`, in order. -/
noncomputable def pPhysQ (v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑ i : Fin 3, ∑ w : Fin 3 → Option (Fin 3),
    pCube (fun y => pD ((List.ofFn w).filterMap id) (fun z => v z i) y ^ 2)

/-- Paper: the `2^m` Leibniz splittings of `L = (a₁,…,a_m)` (each letter goes to the first or to
the second sequence, order kept). -/
def pSplits : List (Fin 3) → List (List (Fin 3) × List (Fin 3))
  | [] => [([], [])]
  | a :: L => (pSplits L).map (fun q => (q.1, a :: q.2)) ++ (pSplits L).map (fun q => (a :: q.1, q.2))

/-- Paper: the tensor de la Vallée Poussin weight `Π_i min(1, max(0, 2 - |k_i|/R))`. -/
noncomputable def pVP (R₀ : ℝ) (k : Fin 3 → ℤ) : ℝ := ∏ i : Fin 3, min 1 (max 0 (2 - |(k i : ℝ)| / R₀))

/-- Paper: `(V_R ∂_j v_i)(x) = Σ_k pVP_R(k) (2πi k_j û_{k,i}) e^{2πi k·x}`. -/
noncomputable def pLowGrad (R₀ : ℝ) (v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (x : EuclideanSpace ℝ (Fin 3)) (i j : Fin 3) : ℂ :=
  ∑' k : Fin 3 → ℤ, (pVP R₀ k : ℂ) * (2 * Real.pi * Complex.I * (k j : ℂ) * pFC v k i) *
    Complex.exp (2 * Real.pi * Complex.I * ∑ l : Fin 3, ((k l : ℝ) : ℂ) * ((x l : ℝ) : ℂ))

/-- Paper: `‖V_R∇v‖_{L^∞} = sup_x Σ_{i,j} |(V_R ∂_j v_i)(x)|`. -/
noncomputable def pLowGradSup (R₀ : ℝ) (v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) :
    ℝ :=
  ⨆ x, ∑ i : Fin 3, ∑ j : Fin 3, ‖pLowGrad R₀ v x i j‖

/-! ### Paper-side statements of the named properties -/

/-- Paper: each Fourier coefficient obeys the projected ODE `û' = F_ν(û)` on `(0,T)`. -/
def pODE (ν : ℝ) : Prop :=
  ∀ (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (p : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ) (T : ℝ), paperSolOn ν u₀ T u p →
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ (k : Fin 3 → ℤ) (i : Fin 3),
      HasDerivAt (fun τ => pFC (u τ) k i) (pNS ν (pFC (u t)) k i) t

/-- Paper: uniform rapid decay of `û(t)` and `F_ν(û(t))` on `[0,T]`. -/
def pDecay (ν : ℝ) : Prop :=
  ∀ (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (p : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ) (T : ℝ), paperSolOn ν u₀ T u p →
    ∀ r : ℝ, ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (k : Fin 3 → ℤ) (i : Fin 3),
      ‖pFC (u t) k i‖ ≤ B₀ * pW (-r) k ∧ ‖pNS ν (pFC (u t)) k i‖ ≤ B₀ * pW (-r) k

/-- Paper: the `H^s` energy identity on `[0,T]`. -/
def pHsId (ν s : ℝ) : Prop :=
  ∀ (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (p : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ) (T : ℝ), paperSolOn ν u₀ T u p →
    ContinuousOn (fun t => pHsSq s (u t)) (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Ioo (0 : ℝ) T,
      Summable (fun q : (Fin 3 → ℤ) × Fin 3 => pW s q.1 *
        (2 * ((starRingEnd ℂ) (pFC (u t) q.1 q.2) * pNS ν (pFC (u t)) q.1 q.2).re)) ∧
      HasDerivAt (fun t => pHsSq s (u t)) (pRate s (pNS ν (pFC (u t))) (pFC (u t))) t

/-- Paper: the `s = 3` physical commutator bound with constant `C₀`. -/
def pPhysComm (C₀ : ℝ) : Prop :=
  ∀ v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3), pDatum v →
    -2 * ∑ i : Fin 3, ∫ x in Set.Icc (0 : Fin 3 → ℝ) 1,
      (pHelm^[3] (fun z => v z i)) ((EuclideanSpace.equiv (Fin 3) ℝ).symm x) *
        pConv v i ((EuclideanSpace.equiv (Fin 3) ℝ).symm x)
      ≤ C₀ * pGradSup v * pHsSq 3 v

/-- Paper: the Fourier-side `H^3` commutator bound with constant `C₀`. -/
def pFourierComm (C₀ : ℝ) : Prop :=
  ∀ v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3), pDatum v →
    Summable (fun q : (Fin 3 → ℤ) × Fin 3 => pW 3 q.1 *
      (2 * ((starRingEnd ℂ) (pFC v q.1 q.2) * pNS 0 (pFC v) q.1 q.2).re)) ∧
    pRate 3 (pNS 0 (pFC v)) (pFC v) ≤ C₀ * pGradSup v * pHsSq 3 v

/-- Paper: the low-frequency vorticity bound. -/
def pLowFreq : Prop :=
  ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ R₀ : ℝ, 2 ≤ R₀ →
    ∀ v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3), pDatum v →
      pLowGradSup R₀ v ≤ K₀ * (1 + Real.log R₀) * ⨆ x, ‖paperCurl v x‖

/-- Paper: `H^s` control along maximal solutions with integrable vorticity (for `ν > 0`). -/
def pHsControl (ν s : ℝ) : Prop :=
  ∀ u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3), pDatum u₀ →
    ∀ (u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (p : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ), pMaximal ν u₀ u p →
      ∀ T : ℝ, paperTstar ν u₀ = (T : EReal) →
        MeasureTheory.IntegrableOn (fun t => ⨆ x, ‖paperCurl (u t) x‖) (Set.Icc 0 T) →
        ∃ M₀ : ℝ, ∀ t ∈ Set.Ico (0 : ℝ) T, pHsNorm s (u t) ≤ M₀

/-- Paper: the `H^s` blow-up alternative (for `ν > 0`). -/
def pBlowup (ν s : ℝ) : Prop :=
  ∀ u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3), pDatum u₀ →
    ∀ (u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (p : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ), pMaximal ν u₀ u p →
      ∀ T : ℝ, paperTstar ν u₀ = (T : EReal) →
        ¬ ∃ M₀ : ℝ, ∀ t ∈ Set.Ico (0 : ℝ) T, pHsNorm s (u t) ≤ M₀

/-! ### The claims -/

/-- `periodicFourierCoeffODE`. -/
def formal_claim_coeffODE : Prop := ∀ ν : ℝ, PeriodicFourierCoeffODE ν
/-- Paper: for every `ν > 0`, the coefficient ODE. -/
def paper_claim_coeffODE : Prop := ∀ ν : ℝ, 0 < ν → pODE ν

/-- `periodicFourierCoeffDecay`. -/
def formal_claim_coeffDecay : Prop := ∀ ν : ℝ, PeriodicFourierCoeffDecay ν
/-- Paper: for every `ν > 0`, rapid decay. -/
def paper_claim_coeffDecay : Prop := ∀ ν : ℝ, 0 < ν → pDecay ν

/-- `periodicFourierHsEnergyIdentity`. -/
def formal_claim_hsIdentity : Prop := ∀ ν s : ℝ, PeriodicFourierHsEnergyIdentity ν s
/-- Paper: for every `ν > 0` and real `s`, the `H^s` identity. -/
def paper_claim_hsIdentity : Prop := ∀ ν s : ℝ, 0 < ν → pHsId ν s

/-- `periodicFourierHsEnergyIdentity_of_coeff`. -/
def formal_claim_hsIdentityOfCoeff : Prop :=
  ∀ ν s : ℝ, PeriodicFourierCoeffODE ν → PeriodicFourierCoeffDecay ν →
    PeriodicFourierHsEnergyIdentity ν s
/-- Paper: the ODE and the decay give the identity. -/
def paper_claim_hsIdentityOfCoeff : Prop :=
  ∀ ν s : ℝ, 0 < ν → pODE ν → pDecay ν → pHsId ν s

/-- `hasSum_rate_three`. -/
def formal_claim_rateThree : Prop :=
  ∀ v : VelocityField, IsPeriodicSmoothInitialData v →
    HasSum (fun q : TorusFourierNS.Mode × Fin 3 => TorusFourierNS.sobW 3 q.1 *
        (2 * ((starRingEnd ℂ) (fourierCoeffVF v q.1 q.2) * nlField (fourierCoeffVF v) q.1 q.2).re))
      (-2 * ∑ i, ∫ x in Set.Icc (0 : Fin 3 → ℝ) 1,
        (helmR^[3] (fun y => v y i)) ((EuclideanSpace.equiv (Fin 3) ℝ).symm x) *
          convR v i ((EuclideanSpace.equiv (Fin 3) ℝ).symm x))
/-- Paper: the `H^3` rate is summable with the physical-space sum. -/
def paper_claim_rateThree : Prop :=
  ∀ v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3), pDatum v →
    HasSum (fun q : (Fin 3 → ℤ) × Fin 3 => pW 3 q.1 *
        (2 * ((starRingEnd ℂ) (pFC v q.1 q.2) * pNS 0 (pFC v) q.1 q.2).re))
      (-2 * ∑ i : Fin 3, ∫ x in Set.Icc (0 : Fin 3 → ℝ) 1,
        (pHelm^[3] (fun z => v z i)) ((EuclideanSpace.equiv (Fin 3) ℝ).symm x) *
          pConv v i ((EuclideanSpace.equiv (Fin 3) ℝ).symm x))

/-- `cellI_ibp`. -/
def formal_claim_ibp : Prop :=
  ∀ φ ψ : EuclideanSpace ℝ (Fin 3) → ℝ, PerR φ → PerR ψ → ∀ j : Fin 3,
    cellI (fun y => pdR j φ y * ψ y) = -cellI (fun y => φ y * pdR j ψ y)
/-- Paper: unit-cell integration by parts. -/
def paper_claim_ibp : Prop :=
  ∀ φ ψ : EuclideanSpace ℝ (Fin 3) → ℝ, pPer φ → pPer ψ → ∀ j : Fin 3,
    pCube (fun y => pd j φ y * ψ y) = -pCube (fun y => φ y * pd j ψ y)

/-- `cellI_ibp'`. -/
def formal_claim_ibpRight : Prop :=
  ∀ φ ψ : EuclideanSpace ℝ (Fin 3) → ℝ, PerR φ → PerR ψ → ∀ j : Fin 3,
    cellI (fun y => φ y * pdR j ψ y) = -cellI (fun y => pdR j φ y * ψ y)
/-- Paper: the mirrored form. -/
def paper_claim_ibpRight : Prop :=
  ∀ φ ψ : EuclideanSpace ℝ (Fin 3) → ℝ, pPer φ → pPer ψ → ∀ j : Fin 3,
    pCube (fun y => φ y * pd j ψ y) = -pCube (fun y => pd j φ y * ψ y)

/-- `DL_mul`. -/
def formal_claim_leibniz : Prop :=
  ∀ f g : EuclideanSpace ℝ (Fin 3) → ℝ, PerR f → PerR g → ∀ L : List (Fin 3),
    DL L (fun y => f y * g y) = fun y => ((splits L).map fun q => DL q.1 f y * DL q.2 g y).sum
/-- Paper: the Leibniz rule for `D^L`. -/
def paper_claim_leibniz : Prop :=
  ∀ f g : EuclideanSpace ℝ (Fin 3) → ℝ, pPer f → pPer g → ∀ L : List (Fin 3),
    pD L (fun y => f y * g y) = fun y => ((pSplits L).map fun q => pD q.1 f y * pD q.2 g y).sum

/-- `gagliardoNirenberg_cell`. -/
def formal_claim_gn : Prop :=
  ∀ g : EuclideanSpace ℝ (Fin 3) → ℝ, PerR g → ∀ M₀ : ℝ, (∀ y, |g y| ≤ M₀) → ∀ a : Fin 3,
    cellI (fun y => pdR a g y ^ 4) ≤ 9 * M₀ ^ 2 * cellI (fun y => pdR a (pdR a g) y ^ 2)
/-- Paper: Gagliardo–Nirenberg on the cell. -/
def paper_claim_gn : Prop :=
  ∀ g : EuclideanSpace ℝ (Fin 3) → ℝ, pPer g → ∀ M₀ : ℝ, (∀ y, |g y| ≤ M₀) → ∀ a : Fin 3,
    pCube (fun y => pd a g y ^ 4) ≤ 9 * M₀ ^ 2 * pCube (fun y => pd a (pd a g) y ^ 2)

/-- `cellI_sq_mul_abs_le`. -/
def formal_claim_sqMulAbs : Prop :=
  ∀ g ρ : EuclideanSpace ℝ (Fin 3) → ℝ, PerR g → PerR ρ → ∀ M₀ : ℝ, 0 ≤ M₀ →
    (∀ y, |g y| ≤ M₀) → ∀ a : Fin 3,
    cellI (fun y => pdR a g y ^ 2 * |ρ y|) ≤
      M₀ / 2 * (9 * cellI (fun y => pdR a (pdR a g) y ^ 2) + cellI (fun y => ρ y ^ 2))
/-- Paper: the weighted Gagliardo–Nirenberg corollary. -/
def paper_claim_sqMulAbs : Prop :=
  ∀ g ρ : EuclideanSpace ℝ (Fin 3) → ℝ, pPer g → pPer ρ → ∀ M₀ : ℝ, 0 ≤ M₀ →
    (∀ y, |g y| ≤ M₀) → ∀ a : Fin 3,
    pCube (fun y => pd a g y ^ 2 * |ρ y|) ≤
      M₀ / 2 * (9 * pCube (fun y => pd a (pd a g) y ^ 2) + pCube (fun y => ρ y ^ 2))

/-- `lower_term_bound`. -/
def formal_claim_lowerTerm : Prop :=
  ∀ v : VelocityField, IsPeriodicSmoothInitialData v → ∀ L : List (Fin 3), L.length ≤ 3 →
    ∀ q : List (Fin 3) × List (Fin 3), q.1.length + q.2.length = L.length → q.1 ≠ [] →
    ∀ i l : Fin 3,
      |cellI (fun y => DL L (fun y => v y i) y *
        (DL q.1 (fun y => v y l) y * DL q.2 (pdR l (fun y => v y i)) y))| ≤
        5 * gradSupNorm v * physQ v
/-- Paper: every lower-order Leibniz term is bounded by `5 ‖∇v‖_∞ Q(v)`. -/
def paper_claim_lowerTerm : Prop :=
  ∀ v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3), pDatum v →
    ∀ L : List (Fin 3), L.length ≤ 3 →
    ∀ q : List (Fin 3) × List (Fin 3), q.1.length + q.2.length = L.length → q.1 ≠ [] →
    ∀ i l : Fin 3,
      |pCube (fun y => pD L (fun z => v z i) y *
        (pD q.1 (fun z => v z l) y * pD q.2 (pd l (fun z => v z i)) y))| ≤
        5 * pGradSup v * pPhysQ v

/-- `periodicHsBlowupAlternative`. -/
def formal_claim_blowup : Prop :=
  ∀ ν s : ℝ, 0 ≤ ν → 5 / 2 < s → PeriodicHsBlowupAlternative ν s
/-- Paper: the blow-up alternative for `ν > 0`, `s > 5/2`. -/
def paper_claim_blowup : Prop := ∀ ν s : ℝ, 0 < ν → 5 / 2 < s → pBlowup ν s

/-- `periodicBKMCriterion_of_hsControl`. -/
def formal_claim_continuation : Prop :=
  ∀ ν s : ℝ, 0 ≤ ν → 5 / 2 < s → PeriodicBKMHsControl ν s → PeriodicBKMCriterion ν
/-- Paper: `H^s` control gives the BKM criterion. -/
def paper_claim_continuation : Prop :=
  ∀ ν s : ℝ, 0 < ν → 5 / 2 < s → pHsControl ν s → pBKMCriterion ν

/-- `periodicPhysicalCommutatorBound`. -/
def formal_claim_physBound : Prop :=
  PeriodicPhysicalCommutatorBound (2 * 64 * 315 * (64 * (4 * Real.pi ^ 2) ^ 3))
/-- Paper: the commutator bound with the explicit constant. -/
def paper_claim_physBound : Prop := pPhysComm (2 * 64 * 315 * (64 * (4 * Real.pi ^ 2) ^ 3))

/-- `word_bound`. -/
def formal_claim_wordBound : Prop :=
  ∀ v : VelocityField, IsPeriodicSmoothInitialData v → ∀ L : List (Fin 3), L.length ≤ 3 →
    |∑ i, cellI (fun y => DL L (fun y => v y i) y * DL L (convR v i) y)| ≤
      315 * gradSupNorm v * physQ v
/-- Paper: the word bound. -/
def paper_claim_wordBound : Prop :=
  ∀ v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3), pDatum v →
    ∀ L : List (Fin 3), L.length ≤ 3 →
    |∑ i : Fin 3, pCube (fun y => pD L (fun z => v z i) y * pD L (pConv v i) y)| ≤
      315 * pGradSup v * pPhysQ v

/-- `physQ_le_hsSq`. -/
def formal_claim_physQLe : Prop :=
  ∀ v : VelocityField, IsPeriodicSmoothInitialData v →
    physQ v ≤ 64 * (4 * Real.pi ^ 2) ^ 3 * hsSq 3 v
/-- Paper: `Q(v) ≤ 64 (4π²)³ ‖v‖²_{H³}`. -/
def paper_claim_physQLe : Prop :=
  ∀ v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3), pDatum v →
    pPhysQ v ≤ 64 * (4 * Real.pi ^ 2) ^ 3 * pHsSq 3 v

/-- `periodicLowFreqVorticityBound`. -/
def formal_claim_lowFreq : Prop := PeriodicLowFreqVorticityBound
/-- Paper: the low-frequency bound. -/
def paper_claim_lowFreq : Prop := pLowFreq

/-- `periodicFourierCommutatorBound_of_physical`. -/
def formal_claim_fourierOfPhys : Prop :=
  ∀ C₀ : ℝ, PeriodicPhysicalCommutatorBound C₀ → PeriodicFourierCommutatorBound 3 C₀
/-- Paper: physical bound ⇒ Fourier bound. -/
def paper_claim_fourierOfPhys : Prop := ∀ C₀ : ℝ, pPhysComm C₀ → pFourierComm C₀

/-- `periodicBKMHsControl_of_physical_lowFreq`. -/
def formal_claim_ctrlOfPhysLow : Prop :=
  ∀ ν : ℝ, (∃ C₀, 0 ≤ C₀ ∧ PeriodicPhysicalCommutatorBound C₀) →
    PeriodicLowFreqVorticityBound → PeriodicBKMHsControl ν 3
/-- Paper: the two bounds give `H³` control for `ν > 0`. -/
def paper_claim_ctrlOfPhysLow : Prop :=
  ∀ ν : ℝ, 0 < ν → (∃ C₀, 0 ≤ C₀ ∧ pPhysComm C₀) → pLowFreq → pHsControl ν 3

/-- `periodicBKMHsControl_three_of_lowFreq`. -/
def formal_claim_ctrlOfLow : Prop :=
  ∀ ν : ℝ, PeriodicLowFreqVorticityBound → PeriodicBKMHsControl ν 3
/-- Paper: the low-frequency bound alone gives `H³` control for `ν > 0`. -/
def paper_claim_ctrlOfLow : Prop := ∀ ν : ℝ, 0 < ν → pLowFreq → pHsControl ν 3

/-- `periodicBKMHsControl_three`. -/
def formal_claim_ctrlThree : Prop := ∀ ν : ℝ, PeriodicBKMHsControl ν 3
/-- Paper: `H³` control for every `ν > 0`. -/
def paper_claim_ctrlThree : Prop := ∀ ν : ℝ, 0 < ν → pHsControl ν 3

/-- `clay_B_exact_of_hsControl`. -/
def formal_claim_clayBOfCtrl : Prop :=
  ∀ ν s : ℝ, 5 / 2 < s → PeriodicBKMHsControl ν s → PeriodicBKMIntegrability ν → Clay_B_exact ν
/-- Paper: `H^s` control and the hypothesis give Statement (B). -/
def paper_claim_clayBOfCtrl : Prop :=
  ∀ ν s : ℝ, 0 < ν → 5 / 2 < s → pHsControl ν s → paperBKMInt ν → pStatementB ν

/-! ### Bridges -/

theorem fc_eq (v : VelocityField) : fourierCoeffVF v = pFC v := rfl

theorem hsNorm_eq (s : ℝ) (v : VelocityField) :
    TorusFourierNS.hsNormField s (fourierCoeffVF v) = pHsNorm s v := rfl

theorem hsSq_eq (s : ℝ) (v : VelocityField) : hsSq s v = pHsSq s v := by
  show TorusFourierNS.hsNormField s (fourierCoeffVF v) ^ 2 = pHsSq s v
  rw [hsNorm_eq]
  exact Real.sq_sqrt (tsum_nonneg fun q => by unfold pW; positivity)

theorem DL_apply (L : List (Fin 3)) (φ : EuclideanSpace ℝ (Fin 3) → ℝ) (y : EuclideanSpace ℝ (Fin 3)) :
    DL L φ y = pD L φ y := by
  rw [TruthGatePaper.DL_eq]

theorem splits_eq : ∀ L : List (Fin 3), splits L = pSplits L
  | [] => rfl
  | a :: L => by simp only [splits, pSplits, splits_eq L]

theorem physQ_eq (v : VelocityField) : physQ v = pPhysQ v := by
  simp only [physQ, pPhysQ, toL, cellI, pCube, DL_apply]

theorem per_iff (φ : EuclideanSpace ℝ (Fin 3) → ℝ) : PerR φ ↔ pPer φ := by
  unfold PerR pPer
  constructor
  · intro h
    exact And.intro h.1 ((TruthGate.periodic_iff φ).2 h.2 : IsZ3Periodic φ)
  · intro h
    exact And.intro h.1 ((TruthGate.periodic_iff φ).1 (h.2 : IsZ3Periodic φ))

theorem ode_iff (ν : ℝ) : PeriodicFourierCoeffODE ν ↔ (0 < ν → pODE ν) := by
  unfold PeriodicFourierCoeffODE pODE
  constructor
  · intro h hν u₀ u p T hs
    exact h hν u₀ u p T ((TruthGate.solOn_iff ν u₀ T u p).2 hs)
  · intro h hν u₀ u p T hs
    exact h hν u₀ u p T ((TruthGate.solOn_iff ν u₀ T u p).1 hs)

theorem decay_iff (ν : ℝ) : PeriodicFourierCoeffDecay ν ↔ (0 < ν → pDecay ν) := by
  unfold PeriodicFourierCoeffDecay pDecay
  constructor
  · intro h hν u₀ u p T hs
    exact h hν u₀ u p T ((TruthGate.solOn_iff ν u₀ T u p).2 hs)
  · intro h hν u₀ u p T hs
    exact h hν u₀ u p T ((TruthGate.solOn_iff ν u₀ T u p).1 hs)

theorem hsid_iff (ν s : ℝ) : PeriodicFourierHsEnergyIdentity ν s ↔ (0 < ν → pHsId ν s) := by
  unfold PeriodicFourierHsEnergyIdentity pHsId
  constructor
  · intro h hν u₀ u p T hs
    have := h hν u₀ u p T ((TruthGate.solOn_iff ν u₀ T u p).2 hs)
    simp only [hsSq_eq] at this
    exact this
  · intro h hν u₀ u p T hs
    have := h hν u₀ u p T ((TruthGate.solOn_iff ν u₀ T u p).1 hs)
    simp only [hsSq_eq]
    exact this

theorem physComm_iff (C₀ : ℝ) : PeriodicPhysicalCommutatorBound C₀ ↔ pPhysComm C₀ := by
  unfold PeriodicPhysicalCommutatorBound pPhysComm
  constructor
  · intro h v hv
    have := h v ((data_iff' v).2 hv)
    rw [hsSq_eq] at this
    exact this
  · intro h v hv
    rw [hsSq_eq]
    exact h v ((data_iff' v).1 hv)

theorem fourierComm_iff (C₀ : ℝ) : PeriodicFourierCommutatorBound 3 C₀ ↔ pFourierComm C₀ := by
  unfold PeriodicFourierCommutatorBound pFourierComm
  constructor
  · intro h v hv
    have := h v ((data_iff' v).2 hv)
    rw [hsSq_eq] at this
    exact this
  · intro h v hv
    rw [hsSq_eq]
    exact h v ((data_iff' v).1 hv)

theorem lowFreq_iff : PeriodicLowFreqVorticityBound ↔ pLowFreq := by
  unfold PeriodicLowFreqVorticityBound pLowFreq
  constructor
  · rintro ⟨K₀, hK, h⟩
    exact ⟨K₀, hK, fun R₀ hR v hv => h R₀ hR v ((data_iff' v).2 hv)⟩
  · rintro ⟨K₀, hK, h⟩
    exact ⟨K₀, hK, fun R₀ hR v hv => h R₀ hR v ((data_iff' v).1 hv)⟩

theorem hsControl_iff (ν s : ℝ) : PeriodicBKMHsControl ν s ↔ (0 < ν → pHsControl ν s) := by
  unfold PeriodicBKMHsControl pHsControl
  constructor
  · intro h hν u₀ hd u p hm T hT
    exact h hν u₀ ((data_iff' u₀).2 hd) u p ((maximal_iff ν u₀ u p).2 hm) T
      (by rw [TruthGate.tstar_eq]; exact hT)
  · intro h hν u₀ hd u p hm T hT
    exact h hν u₀ ((data_iff' u₀).1 hd) u p ((maximal_iff ν u₀ u p).1 hm) T
      (by rw [← TruthGate.tstar_eq]; exact hT)

theorem blowup_iff (ν s : ℝ) : PeriodicHsBlowupAlternative ν s ↔ (0 < ν → pBlowup ν s) := by
  unfold PeriodicHsBlowupAlternative pBlowup
  constructor
  · intro h hν u₀ hd u p hm T hT
    exact h hν u₀ ((data_iff' u₀).2 hd) u p ((maximal_iff ν u₀ u p).2 hm) T
      (by rw [TruthGate.tstar_eq]; exact hT)
  · intro h hν u₀ hd u p hm T hT
    exact h hν u₀ ((data_iff' u₀).1 hd) u p ((maximal_iff ν u₀ u p).1 hm) T
      (by rw [← TruthGate.tstar_eq]; exact hT)

/-! ### Correspondences -/

theorem intended_correspondence_coeffODE : formal_claim_coeffODE ↔ paper_claim_coeffODE := by
  constructor
  · intro h ν hν
    exact (ode_iff ν).1 (h ν) hν
  · intro h ν
    exact (ode_iff ν).2 (h ν)

theorem intended_correspondence_coeffDecay : formal_claim_coeffDecay ↔ paper_claim_coeffDecay := by
  constructor
  · intro h ν hν
    exact (decay_iff ν).1 (h ν) hν
  · intro h ν
    exact (decay_iff ν).2 (h ν)

theorem intended_correspondence_hsIdentity : formal_claim_hsIdentity ↔ paper_claim_hsIdentity := by
  constructor
  · intro h ν s hν
    exact (hsid_iff ν s).1 (h ν s) hν
  · intro h ν s
    exact (hsid_iff ν s).2 (h ν s)

theorem intended_correspondence_hsIdentityOfCoeff :
    formal_claim_hsIdentityOfCoeff ↔ paper_claim_hsIdentityOfCoeff := by
  constructor
  · intro h ν s hν ho hd
    exact (hsid_iff ν s).1 (h ν s ((ode_iff ν).2 fun _ => ho) ((decay_iff ν).2 fun _ => hd)) hν
  · intro h ν s ho hd
    exact (hsid_iff ν s).2 fun hν => h ν s hν ((ode_iff ν).1 ho hν) ((decay_iff ν).1 hd hν)

theorem intended_correspondence_rateThree : formal_claim_rateThree ↔ paper_claim_rateThree := by
  constructor
  · intro h v hv
    exact h v ((data_iff' v).2 hv)
  · intro h v hv
    exact h v ((data_iff' v).1 hv)

theorem intended_correspondence_ibp : formal_claim_ibp ↔ paper_claim_ibp := by
  constructor
  · intro h φ ψ hφ hψ j
    exact h φ ψ ((per_iff φ).2 hφ) ((per_iff ψ).2 hψ) j
  · intro h φ ψ hφ hψ j
    exact h φ ψ ((per_iff φ).1 hφ) ((per_iff ψ).1 hψ) j

theorem intended_correspondence_ibpRight : formal_claim_ibpRight ↔ paper_claim_ibpRight := by
  constructor
  · intro h φ ψ hφ hψ j
    exact h φ ψ ((per_iff φ).2 hφ) ((per_iff ψ).2 hψ) j
  · intro h φ ψ hφ hψ j
    exact h φ ψ ((per_iff φ).1 hφ) ((per_iff ψ).1 hψ) j

theorem intended_correspondence_leibniz : formal_claim_leibniz ↔ paper_claim_leibniz := by
  constructor
  · intro h f g hf hg L
    have := h f g ((per_iff f).2 hf) ((per_iff g).2 hg) L
    simp only [TruthGatePaper.DL_eq, DL_apply, splits_eq] at this
    exact this
  · intro h f g hf hg L
    have := h f g ((per_iff f).1 hf) ((per_iff g).1 hg) L
    simp only [TruthGatePaper.DL_eq, DL_apply, splits_eq]
    exact this

theorem intended_correspondence_gn : formal_claim_gn ↔ paper_claim_gn := by
  constructor
  · intro h g hg M₀ hM a
    exact h g ((per_iff g).2 hg) M₀ hM a
  · intro h g hg M₀ hM a
    exact h g ((per_iff g).1 hg) M₀ hM a

theorem intended_correspondence_sqMulAbs : formal_claim_sqMulAbs ↔ paper_claim_sqMulAbs := by
  constructor
  · intro h g ρ hg hρ M₀ hM0 hM a
    exact h g ρ ((per_iff g).2 hg) ((per_iff ρ).2 hρ) M₀ hM0 hM a
  · intro h g ρ hg hρ M₀ hM0 hM a
    exact h g ρ ((per_iff g).1 hg) ((per_iff ρ).1 hρ) M₀ hM0 hM a

theorem intended_correspondence_lowerTerm : formal_claim_lowerTerm ↔ paper_claim_lowerTerm := by
  constructor
  · intro h v hv L hL q hq hq1 i l
    have := h v ((data_iff' v).2 hv) L hL q hq hq1 i l
    simp only [DL_apply, physQ_eq] at this
    exact this
  · intro h v hv L hL q hq hq1 i l
    simp only [DL_apply, physQ_eq]
    exact h v ((data_iff' v).1 hv) L hL q hq hq1 i l

theorem intended_correspondence_blowup : formal_claim_blowup ↔ paper_claim_blowup := by
  constructor
  · intro h ν s hν hs
    exact (blowup_iff ν s).1 (h ν s hν.le hs) hν
  · intro h ν s _ hs
    exact (blowup_iff ν s).2 fun hν => h ν s hν hs

theorem intended_correspondence_continuation :
    formal_claim_continuation ↔ paper_claim_continuation := by
  constructor
  · intro h ν s hν hs hc
    exact (crit_iff ν).1 (h ν s hν.le hs ((hsControl_iff ν s).2 fun _ => hc)) hν
  · intro h ν s _ hs hc
    exact (crit_iff ν).2 fun hν => h ν s hν hs ((hsControl_iff ν s).1 hc hν)

theorem intended_correspondence_physBound : formal_claim_physBound ↔ paper_claim_physBound :=
  physComm_iff _

theorem intended_correspondence_wordBound : formal_claim_wordBound ↔ paper_claim_wordBound := by
  constructor
  · intro h v hv L hL
    have := h v ((data_iff' v).2 hv) L hL
    simp only [DL_apply, physQ_eq] at this
    exact this
  · intro h v hv L hL
    simp only [DL_apply, physQ_eq]
    exact h v ((data_iff' v).1 hv) L hL

theorem intended_correspondence_physQLe : formal_claim_physQLe ↔ paper_claim_physQLe := by
  constructor
  · intro h v hv
    have := h v ((data_iff' v).2 hv)
    rw [physQ_eq, hsSq_eq] at this
    exact this
  · intro h v hv
    rw [physQ_eq, hsSq_eq]
    exact h v ((data_iff' v).1 hv)

theorem intended_correspondence_lowFreq : formal_claim_lowFreq ↔ paper_claim_lowFreq :=
  lowFreq_iff

theorem intended_correspondence_fourierOfPhys :
    formal_claim_fourierOfPhys ↔ paper_claim_fourierOfPhys := by
  constructor
  · intro h C₀ hp
    exact (fourierComm_iff C₀).1 (h C₀ ((physComm_iff C₀).2 hp))
  · intro h C₀ hp
    exact (fourierComm_iff C₀).2 (h C₀ ((physComm_iff C₀).1 hp))

theorem intended_correspondence_ctrlOfPhysLow :
    formal_claim_ctrlOfPhysLow ↔ paper_claim_ctrlOfPhysLow := by
  constructor
  · rintro h ν hν ⟨C₀, hC, hp⟩ hl
    exact (hsControl_iff ν 3).1 (h ν ⟨C₀, hC, (physComm_iff C₀).2 hp⟩ (lowFreq_iff.2 hl)) hν
  · rintro h ν ⟨C₀, hC, hp⟩ hl
    exact (hsControl_iff ν 3).2 fun hν => h ν hν ⟨C₀, hC, (physComm_iff C₀).1 hp⟩ (lowFreq_iff.1 hl)

theorem intended_correspondence_ctrlOfLow : formal_claim_ctrlOfLow ↔ paper_claim_ctrlOfLow := by
  constructor
  · intro h ν hν hl
    exact (hsControl_iff ν 3).1 (h ν (lowFreq_iff.2 hl)) hν
  · intro h ν hl
    exact (hsControl_iff ν 3).2 fun hν => h ν hν (lowFreq_iff.1 hl)

theorem intended_correspondence_ctrlThree : formal_claim_ctrlThree ↔ paper_claim_ctrlThree := by
  constructor
  · intro h ν hν
    exact (hsControl_iff ν 3).1 (h ν) hν
  · intro h ν
    exact (hsControl_iff ν 3).2 (h ν)

theorem intended_correspondence_clayBOfCtrl : formal_claim_clayBOfCtrl ↔ paper_claim_clayBOfCtrl := by
  constructor
  · intro h ν s hν hs hc hi
    exact (clayB_iff ν).1 (h ν s hs ((hsControl_iff ν s).2 fun _ => hc)
      ((TruthGate.bkmInt_iff ν).2 hi)) hν
  · intro h ν s hs hc hi
    exact (clayB_iff ν).2 fun hν => h ν s hν hs ((hsControl_iff ν s).1 hc hν)
      ((TruthGate.bkmInt_iff ν).1 hi)
-- TRUTH-GATE LOCK END

/-! ### The repository theorems prove the formal claims; the paper claims follow by transport -/

theorem formal_claim_holds_coeffODE : formal_claim_coeffODE := fun ν => periodicFourierCoeffODE ν
theorem paper_claim_holds_coeffODE : paper_claim_coeffODE :=
  intended_correspondence_coeffODE.mp formal_claim_holds_coeffODE

theorem formal_claim_holds_coeffDecay : formal_claim_coeffDecay :=
  fun ν => periodicFourierCoeffDecay ν
theorem paper_claim_holds_coeffDecay : paper_claim_coeffDecay :=
  intended_correspondence_coeffDecay.mp formal_claim_holds_coeffDecay

theorem formal_claim_holds_hsIdentity : formal_claim_hsIdentity :=
  fun ν s => periodicFourierHsEnergyIdentity ν s
theorem paper_claim_holds_hsIdentity : paper_claim_hsIdentity :=
  intended_correspondence_hsIdentity.mp formal_claim_holds_hsIdentity

theorem formal_claim_holds_hsIdentityOfCoeff : formal_claim_hsIdentityOfCoeff :=
  fun _ s ho hd => periodicFourierHsEnergyIdentity_of_coeff s ho hd
theorem paper_claim_holds_hsIdentityOfCoeff : paper_claim_hsIdentityOfCoeff :=
  intended_correspondence_hsIdentityOfCoeff.mp formal_claim_holds_hsIdentityOfCoeff

theorem formal_claim_holds_rateThree : formal_claim_rateThree := fun _ hv => hasSum_rate_three hv
theorem paper_claim_holds_rateThree : paper_claim_rateThree :=
  intended_correspondence_rateThree.mp formal_claim_holds_rateThree

theorem formal_claim_holds_ibp : formal_claim_ibp := fun _ _ h h' j => cellI_ibp h h' j
theorem paper_claim_holds_ibp : paper_claim_ibp :=
  intended_correspondence_ibp.mp formal_claim_holds_ibp

theorem formal_claim_holds_ibpRight : formal_claim_ibpRight := fun _ _ h h' j => cellI_ibp' h h' j
theorem paper_claim_holds_ibpRight : paper_claim_ibpRight :=
  intended_correspondence_ibpRight.mp formal_claim_holds_ibpRight

theorem formal_claim_holds_leibniz : formal_claim_leibniz := fun _ _ hf hg L => DL_mul hf hg L
theorem paper_claim_holds_leibniz : paper_claim_leibniz :=
  intended_correspondence_leibniz.mp formal_claim_holds_leibniz

theorem formal_claim_holds_gn : formal_claim_gn :=
  fun _ hg _ hM a => gagliardoNirenberg_cell hg hM a
theorem paper_claim_holds_gn : paper_claim_gn :=
  intended_correspondence_gn.mp formal_claim_holds_gn

theorem formal_claim_holds_sqMulAbs : formal_claim_sqMulAbs :=
  fun _ _ hg hρ _ hM0 hM a => cellI_sq_mul_abs_le hg hρ hM0 hM a
theorem paper_claim_holds_sqMulAbs : paper_claim_sqMulAbs :=
  intended_correspondence_sqMulAbs.mp formal_claim_holds_sqMulAbs

theorem formal_claim_holds_lowerTerm : formal_claim_lowerTerm :=
  fun _ hv L hL q hq hq1 i l => lower_term_bound hv L hL q hq hq1 i l
theorem paper_claim_holds_lowerTerm : paper_claim_lowerTerm :=
  intended_correspondence_lowerTerm.mp formal_claim_holds_lowerTerm

theorem formal_claim_holds_blowup : formal_claim_blowup :=
  fun _ s hν hs => periodicHsBlowupAlternative (s := s) hν hs
theorem paper_claim_holds_blowup : paper_claim_blowup :=
  intended_correspondence_blowup.mp formal_claim_holds_blowup

theorem formal_claim_holds_continuation : formal_claim_continuation :=
  fun _ _ hν hs h => periodicBKMCriterion_of_hsControl hν hs h
theorem paper_claim_holds_continuation : paper_claim_continuation :=
  intended_correspondence_continuation.mp formal_claim_holds_continuation

theorem formal_claim_holds_physBound : formal_claim_physBound := periodicPhysicalCommutatorBound
theorem paper_claim_holds_physBound : paper_claim_physBound :=
  intended_correspondence_physBound.mp formal_claim_holds_physBound

theorem formal_claim_holds_wordBound : formal_claim_wordBound :=
  fun _ hv L hL => word_bound hv L hL
theorem paper_claim_holds_wordBound : paper_claim_wordBound :=
  intended_correspondence_wordBound.mp formal_claim_holds_wordBound

theorem formal_claim_holds_physQLe : formal_claim_physQLe := fun _ hv => physQ_le_hsSq hv
theorem paper_claim_holds_physQLe : paper_claim_physQLe :=
  intended_correspondence_physQLe.mp formal_claim_holds_physQLe

theorem formal_claim_holds_lowFreq : formal_claim_lowFreq := periodicLowFreqVorticityBound
theorem paper_claim_holds_lowFreq : paper_claim_lowFreq :=
  intended_correspondence_lowFreq.mp formal_claim_holds_lowFreq

theorem formal_claim_holds_fourierOfPhys : formal_claim_fourierOfPhys :=
  fun _ hP => periodicFourierCommutatorBound_of_physical hP
theorem paper_claim_holds_fourierOfPhys : paper_claim_fourierOfPhys :=
  intended_correspondence_fourierOfPhys.mp formal_claim_holds_fourierOfPhys

theorem formal_claim_holds_ctrlOfPhysLow : formal_claim_ctrlOfPhysLow :=
  fun ν hP hL => periodicBKMHsControl_of_physical_lowFreq ν hP hL
theorem paper_claim_holds_ctrlOfPhysLow : paper_claim_ctrlOfPhysLow :=
  intended_correspondence_ctrlOfPhysLow.mp formal_claim_holds_ctrlOfPhysLow

theorem formal_claim_holds_ctrlOfLow : formal_claim_ctrlOfLow :=
  fun ν hL => periodicBKMHsControl_three_of_lowFreq ν hL
theorem paper_claim_holds_ctrlOfLow : paper_claim_ctrlOfLow :=
  intended_correspondence_ctrlOfLow.mp formal_claim_holds_ctrlOfLow

theorem formal_claim_holds_ctrlThree : formal_claim_ctrlThree := fun ν => periodicBKMHsControl_three ν
theorem paper_claim_holds_ctrlThree : paper_claim_ctrlThree :=
  intended_correspondence_ctrlThree.mp formal_claim_holds_ctrlThree

theorem formal_claim_holds_clayBOfCtrl : formal_claim_clayBOfCtrl :=
  fun ν s hs hc hi => clay_B_exact_of_hsControl ν s hs hc hi
theorem paper_claim_holds_clayBOfCtrl : paper_claim_clayBOfCtrl :=
  intended_correspondence_clayBOfCtrl.mp formal_claim_holds_clayBOfCtrl

end TruthGatePaper2
