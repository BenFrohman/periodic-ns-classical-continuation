/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import PeriodicNSContinuation.Semantics
import PeriodicNSContinuation.IntegrabilityAttack
import PeriodicNSContinuation.Energy
import PeriodicNSContinuation.Maximal
import PeriodicNSContinuation.Route
import PeriodicNSContinuation.Parseval
import PeriodicNSContinuation.KatoPonce

/-!
# Truth Gate: additional lock "paper-statements" (see `TRUTH_GATE.md`)

PAPER_PATH: paper/periodic-ns-classical-continuation.tex
PAPER_SHA256: effd6bb926e424b41076cac25c4363a8d1011b48d729811b805f5d2bc764df2d
PAPER_SECTION: Sections "Proved results (no hypothesis Props)", "Conditional results" and "Further reductions of the open hypothesis"

Each claim `X` below has `formal_claim_X` (the statement of the repository theorem(s)),
`paper_claim_X` (an independent transcription of the quoted paper sentence, using only Mathlib and the
author-signed-off paper-side notions `paperSolOn`, `paperTstar`, `paperCurl`, `paperBKMInt` of the
main lock), and `intended_correspondence_X : formal_claim_X ↔ paper_claim_X`.

The quoted sentences (verbatim from the paper):

PAPER_QUOTE_BEGIN
Since \lean{PeriodicLocalExistence}~$\nu$ begins with the hypothesis $0<\nu$, the theorem states: for every $\nu>0$ and every smooth, divergence-free, $\mathbb{Z}^3$-periodic $u_0$ there are a real $T>0$ and a pair $(u,p)$ that is a smooth periodic solution on $[0,T]$ with data $u_0$ (as defined in Section~\ref{sec:conditional}). For $\nu=0$ it says nothing; local existence for the Euler equations is not claimed.
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\lean{periodicEnergyDifferenceEstimate}\coined: let $\nu\ge0$ and let $(u,p)$ and $(v,q)$ be smooth periodic solutions on $[0,T]$ with the same data $u_0$ (as defined in Section~\ref{sec:conditional}; the definition makes sense for every real $\nu$). Then there are functions $E,E'\colon\mathbb{R}\to\mathbb{R}$ and a real $L$ such that $E$ is continuous on $[0,T]$; for every $t\in[0,T)$, $E'(t)$ is the right derivative of $E$ at $t$ and $E'(t)\le L\,E(t)$; $E(0)\le0$; and $u(t)=v(t)$ for every $t\in[0,T]$ with $E(t)\le0$.
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
With Gr\"onwall (\lean{eq_zero_of_deriv_le_mul}\coined, \lean{periodicVelocityUniqueness_of_energy}\coined) this gives uniqueness: for $\nu\ge0$, if $(u,p)$ and $(v,q)$ are smooth periodic solutions on $[0,T]$ with the same data $u_0$, then $u(t)=v(t)$ for every $t\in[0,T]$.
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
Gluing (\lean{Corrected.periodicMaximalSolution_of_uniqueness}\coined) then gives maximal solutions: for every $\nu>0$ and every smooth, divergence-free, $\mathbb{Z}^3$-periodic $u_0$ there is a pair $(u,p)$ that is a smooth periodic solution on $[0,T]$ with data $u_0$ for every real $T$ with $0<T<\Tstar(u_0)$.
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\lean{hasSum_prod_cubeCoeff}\coined{} (\file{Parseval.lean}): let $f,g\colon\mathbb{R}^3\to\mathbb{C}$ be continuous with $f(x+n)=f(x)$ and $g(x+n)=g(x)$ for all $x\in\mathbb{R}^3$ and $n\in\mathbb{Z}^3$, and let $\hat f_k=\int_{[0,1]^3}f(x)\,e^{-2\pi i\,k\cdot x}\dd x$ for $k\in\mathbb{Z}^3$ (likewise $\hat g_k$). Then the series below converges unconditionally (it is summable over $\mathbb{Z}^3$) and
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\lean{top_term_zero}\coined: for every smooth, divergence-free, $\mathbb{Z}^3$-periodic $v$ and every finite sequence $L=(a_1,\dots,a_m)$ of coordinate directions, with $D^L=\partial_{a_1}\cdots\partial_{a_m}$ ($D^L$ is the identity when $m=0$), $\displaystyle\sum_{i,l}\int_{[0,1]^3} D^L v_i\, v_l\, D^L\partial_l v_i\dd x = 0$, because $\Div v=0$ (transport cancellation).
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
Spelled out, \lean{periodicBKMCriterion} states: for every $\nu>0$, every smooth, divergence-free, $\mathbb{Z}^3$-periodic $u_0$ and every pair $(u,p)$ that is a smooth periodic solution on $[0,T']$ with data $u_0$ for every real $T'$ with $0<T'<\Tstar(u_0)$, if $\Tstar(u_0)=T$ for a real $T$, then $t\mapsto\norm{\omega(t)}_{L^\infty}=\sup_{x\in\mathbb{R}^3}\abs{(\nabla\times u(t))(x)}$ is not integrable on $[0,T]$.
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
Spelled out, \lean{clay_B_exact_of_bkm} states: for every $\nu>0$, if the BKM criterion holds for $\nu$ in the spelled-out form above and the hypothesis \lean{PeriodicBKMIntegrability}~$\nu$ holds in the form stated in this section, then Statement~(B) holds for $\nu$, read in the model of Section~\ref{sec:model}. \lean{clay_B_exact_of_corrected_route'} states the same with, as a further hypothesis, local existence for $\nu$ in the form stated in Section~\ref{sec:proved}.
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\lean{integrableOn_vorticity_of_lt_tstar} (proved): for $\nu>0$, every field $u_0$, every pair $(u,p)$ that is a smooth periodic solution on $[0,T']$ with data $u_0$ for every real $T'$ with $0<T'<\Tstar(u_0)$, and every real $T<\Tstar(u_0)$, the function $t\mapsto\norm{\omega(t)}_{L^\infty}$ is integrable on $[0,T]$; in particular $\int_0^T\norm{\omega}_{L^\infty}\dd t<\infty$.
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\lean{periodicBKMIntegrability_iff_globalLifespan} (proved): for every real $\nu$, \lean{PeriodicBKMIntegrability}~$\nu$ holds iff \lean{PeriodicGlobalLifespan}~$\nu$, which states: if $\nu>0$, then $\Tstar(u_0)=\infty$ for every smooth, divergence-free, $\mathbb{Z}^3$-periodic $u_0$. The open hypothesis is therefore exactly global existence.
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\lean{clay_B_exact_of_globalLifespan} (proved, conditional): for every $\nu>0$, if $\Tstar(u_0)=\infty$ for every smooth, divergence-free, $\mathbb{Z}^3$-periodic $u_0$, then Statement~(B) holds for $\nu$.
PAPER_QUOTE_END

Recorded discrepancies (the paper was corrected to what Lean states; no Lean statement was changed):
* local existence: the paper said "for `ν ≥ 0`"; `PeriodicLocalExistence ν` starts with `0 < ν`, so
  the content is for `ν > 0` only, and `ν = 0` is vacuous.
* energy difference: the paper said `E(t) = ∫_{[0,1]³} |u - v|²` satisfies `E' ≤ 2CE`; the Lean
  statement is existential in `E, E', L` and does not fix `E` (the proof uses the cell integral).

Scope: this lock covers the claims listed in `TRUTH_GATE.lock` (`additional_locks`). It is not yet the
whole paper; the statements still outside every lock are listed there. Nothing here proves Statement
(B), global regularity, or any Clay problem.
-/

namespace TruthGatePaper

open scoped ContDiff Gradient
open FeffermanClayNS NavierStokes3D PeriodicNSContinuation TruthGate MeasureTheory

-- TRUTH-GATE LOCK BEGIN
/-! ### Paper-side notions (Mathlib only, plus the main lock's paper-side notions) -/

/-- Paper: `u₀` is smooth, divergence-free and `ℤ³`-periodic. -/
def pDatum (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) u₀ ∧
    (∀ x, ∑ i : Fin 3, fderiv ℝ (fun y => u₀ y i) x (EuclideanSpace.single i 1) = 0) ∧
    (∀ x (j : Fin 3), u₀ (x + EuclideanSpace.single j 1) = u₀ x)

/-- Paper: `(u, p)` is a smooth periodic solution on `[0, T]` with data `u₀` for every real `T`
with `0 < T < T*(u₀)`. -/
def pMaximal (ν : ℝ) (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (p : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ) : Prop :=
  ∀ T : ℝ, 0 < T → (T : EReal) < paperTstar ν u₀ → paperSolOn ν u₀ T u p

/-- Paper (Section "Proved results"): local existence for `ν`. -/
def pLocalExistence (ν : ℝ) : Prop :=
  ∀ u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3), pDatum u₀ →
    ∃ (T : ℝ) (u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (p : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ), paperSolOn ν u₀ T u p

/-- Paper (Section "Conditional results"): the BKM criterion for `ν`, spelled out. -/
def pBKMCriterion (ν : ℝ) : Prop :=
  ∀ u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3), pDatum u₀ →
    ∀ (u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (p : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ), pMaximal ν u₀ u p →
      ∀ T : ℝ, paperTstar ν u₀ = (T : EReal) →
        ¬ MeasureTheory.IntegrableOn (fun t => ⨆ x, ‖paperCurl (u t) x‖) (Set.Icc 0 T)

/-- Paper: Statement (B) for `ν`, read in the model of Section "Modelling of the torus". -/
def pStatementB (ν : ℝ) : Prop :=
  ∀ u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3), pDatum u₀ →
    ∃ (u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (p : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ),
      ContDiffOn ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => u q.1 q.2)
          (Set.Ici (0 : ℝ) ×ˢ Set.univ) ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => p q.1 q.2)
          (Set.Ici (0 : ℝ) ×ˢ Set.univ) ∧
      (∀ t ≥ (0 : ℝ), ∀ x,
        derivWithin (fun s => u s x) (Set.Ici (0 : ℝ)) t + fderiv ℝ (u t) x (u t x) =
          ν • ∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ (u t) y (EuclideanSpace.single i 1)) x
              (EuclideanSpace.single i 1) - ∇ (p t) x) ∧
      (∀ t ≥ (0 : ℝ), ∀ x,
        ∑ i : Fin 3, fderiv ℝ (fun y => u t y i) x (EuclideanSpace.single i 1) = 0) ∧
      (∀ x, u 0 x = u₀ x) ∧
      (∀ t ≥ (0 : ℝ), ∀ x (j : Fin 3),
        u t (x + EuclideanSpace.single j 1) = u t x ∧ p t (x + EuclideanSpace.single j 1) = p t x)

/-- Paper: `f̂_k = ∫_{[0,1]³} f(x) e^{-2πi k·x} dx`, with `k·x = Σⱼ kⱼ xⱼ` a real number. -/
noncomputable def pCoeff (f : (Fin 3 → ℝ) → ℂ) (k : Fin 3 → ℤ) : ℂ :=
  ∫ x in Set.Icc (0 : Fin 3 → ℝ) 1,
    f x * Complex.exp (-(2 * Real.pi * Complex.I) * ((∑ j : Fin 3, (k j : ℝ) * x j : ℝ) : ℂ))

/-- Paper: `D^L = ∂_{a₁} ⋯ ∂_{aₘ}` for `L = (a₁, …, aₘ)` (the identity for the empty sequence). -/
noncomputable def pD (L : List (Fin 3))
    (φ : EuclideanSpace ℝ (Fin 3) → ℝ) : EuclideanSpace ℝ (Fin 3) → ℝ :=
  L.foldr (fun a ψ => fun y => fderiv ℝ ψ y (EuclideanSpace.single a 1)) φ

/-- Paper: `∫_{[0,1]³} Φ dx`, the unit cube in coordinates. -/
noncomputable def pCube (Φ : EuclideanSpace ℝ (Fin 3) → ℝ) : ℝ :=
  ∫ x in Set.Icc (0 : Fin 3 → ℝ) 1, Φ ((EuclideanSpace.equiv (Fin 3) ℝ).symm x)

/-! ### The claims -/

/-- `periodicLocalExistence_of_nonneg`. -/
def formal_claim_localExistence : Prop := ∀ ν : ℝ, 0 ≤ ν → PeriodicLocalExistence ν
/-- Paper: for every `ν > 0`, local existence. -/
def paper_claim_localExistence : Prop := ∀ ν : ℝ, 0 < ν → pLocalExistence ν

/-- `Corrected.periodicEnergyDifferenceEstimate`. -/
def formal_claim_energyDifference : Prop :=
  ∀ ν : ℝ, 0 ≤ ν → Corrected.PeriodicEnergyDifferenceEstimate ν
/-- Paper: the energy-difference statement, as quoted. -/
def paper_claim_energyDifference : Prop :=
  ∀ ν : ℝ, 0 ≤ ν → ∀ (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (T : ℝ)
    (u v : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (p q : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ),
    paperSolOn ν u₀ T u p → paperSolOn ν u₀ T v q →
    ∃ (E E' : ℝ → ℝ) (L : ℝ), ContinuousOn E (Set.Icc 0 T) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt E (E' t) (Set.Ici t) t) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) T, E' t ≤ L * E t) ∧ E 0 ≤ 0 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, E t ≤ 0 → u t = v t)

/-- `Corrected.periodicVelocityUniqueness_of_energy` with `periodicEnergyDifferenceEstimate`. -/
def formal_claim_uniqueness : Prop :=
  ∀ ν : ℝ, 0 ≤ ν → Corrected.PeriodicVelocityUniqueness ν
/-- Paper: uniqueness for `ν ≥ 0`. -/
def paper_claim_uniqueness : Prop :=
  ∀ ν : ℝ, 0 ≤ ν → ∀ (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (T : ℝ)
    (u v : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (p q : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ),
    paperSolOn ν u₀ T u p → paperSolOn ν u₀ T v q → ∀ t ∈ Set.Icc (0 : ℝ) T, u t = v t

/-- `Corrected.periodicMaximalSolution_of_uniqueness` (with uniqueness for `ν ≥ 0`). -/
def formal_claim_maximal : Prop := ∀ ν : ℝ, PeriodicMaximalSolution ν
/-- Paper: maximal solutions for `ν > 0`. -/
def paper_claim_maximal : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3), pDatum u₀ →
    ∃ (u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (p : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ), pMaximal ν u₀ u p

/-- `hasSum_prod_cubeCoeff`. -/
def formal_claim_parseval : Prop :=
  ∀ f g : (Fin 3 → ℝ) → ℂ, Continuous f → Continuous g →
    (∀ y (n : Fin 3 → ℤ), f (y + fun j => (n j : ℝ)) = f y) →
    (∀ y (n : Fin 3 → ℤ), g (y + fun j => (n j : ℝ)) = g y) →
    HasSum (fun k => (starRingEnd ℂ) (cubeCoeff f k) * cubeCoeff g k)
      (∫ x in Set.Icc (0 : Fin 3 → ℝ) 1, (starRingEnd ℂ) (f x) * g x)
/-- Paper: Parseval on the unit cube (summable, with the stated sum). -/
def paper_claim_parseval : Prop :=
  ∀ f g : (Fin 3 → ℝ) → ℂ, Continuous f → Continuous g →
    (∀ (x : Fin 3 → ℝ) (n : Fin 3 → ℤ), f (x + fun j => (n j : ℝ)) = f x) →
    (∀ (x : Fin 3 → ℝ) (n : Fin 3 → ℤ), g (x + fun j => (n j : ℝ)) = g x) →
    Summable (fun k : Fin 3 → ℤ => (starRingEnd ℂ) (pCoeff f k) * pCoeff g k) ∧
      ∑' k : Fin 3 → ℤ, (starRingEnd ℂ) (pCoeff f k) * pCoeff g k =
        ∫ x in Set.Icc (0 : Fin 3 → ℝ) 1, (starRingEnd ℂ) (f x) * g x

/-- `top_term_zero`. -/
def formal_claim_topTerm : Prop :=
  ∀ v : VelocityField, IsPeriodicSmoothInitialData v → ∀ L : List (Fin 3),
    ∑ i, ∑ l, cellI (fun y => DL L (fun y => v y i) y *
        (DL [] (fun y => v y l) y * DL L (pdR l (fun y => v y i)) y)) = 0
/-- Paper: the top-order term vanishes. -/
def paper_claim_topTerm : Prop :=
  ∀ v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3), pDatum v → ∀ L : List (Fin 3),
    ∑ i : Fin 3, ∑ l : Fin 3, pCube (fun y => pD L (fun z => v z i) y *
        (v y l * pD L (fun z => fderiv ℝ (fun w => v w i) z (EuclideanSpace.single l 1)) y)) = 0

/-- `periodicBKMCriterion`. -/
def formal_claim_bkmCriterion : Prop := ∀ ν : ℝ, PeriodicBKMCriterion ν
/-- Paper: the BKM criterion for every `ν > 0`, spelled out. -/
def paper_claim_bkmCriterion : Prop := ∀ ν : ℝ, 0 < ν → pBKMCriterion ν

/-- `integrableOn_vorticity_of_lt_tstar`. -/
def formal_claim_integrableBelow : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ (u₀ : VelocityField) (u : TimeDependentVelocity) (p : TimeDependentPressure),
    IsPeriodicMaximalSolution ν u₀ u p → ∀ T : ℝ, (T : EReal) < periodicTstar ν u₀ →
      IntegrableOn (fun t => vorticity_sup_norm (vorticity (u t))) (Set.Icc 0 T)
/-- Paper: integrability below `T*`. -/
def paper_claim_integrableBelow : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (p : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ), pMaximal ν u₀ u p →
    ∀ T : ℝ, (T : EReal) < paperTstar ν u₀ →
      MeasureTheory.IntegrableOn (fun t => ⨆ x, ‖paperCurl (u t) x‖) (Set.Icc 0 T)

/-- `periodicBKMIntegrability_iff_globalLifespan`. -/
def formal_claim_bkmIffGlobal : Prop :=
  ∀ ν : ℝ, (PeriodicBKMIntegrability ν ↔ PeriodicGlobalLifespan ν)
/-- Paper: the hypothesis holds iff `T* = ∞` for all data (when `ν > 0`). -/
def paper_claim_bkmIffGlobal : Prop :=
  ∀ ν : ℝ, (paperBKMInt ν ↔ (0 < ν → ∀ u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
    pDatum u₀ → paperTstar ν u₀ = ⊤))

/-- `clay_B_exact_of_globalLifespan`. -/
def formal_claim_clayBOfGlobal : Prop := ∀ ν : ℝ, PeriodicGlobalLifespan ν → Clay_B_exact ν
/-- Paper: global lifespan gives Statement (B). -/
def paper_claim_clayBOfGlobal : Prop :=
  ∀ ν : ℝ, 0 < ν → (∀ u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
    pDatum u₀ → paperTstar ν u₀ = ⊤) → pStatementB ν

/-- `clay_B_exact_of_bkm`. -/
def formal_claim_clayBOfBKM : Prop :=
  ∀ ν : ℝ, PeriodicBKMCriterion ν → PeriodicBKMIntegrability ν → Clay_B_exact ν
/-- Paper: the BKM criterion and the hypothesis give Statement (B). -/
def paper_claim_clayBOfBKM : Prop :=
  ∀ ν : ℝ, 0 < ν → pBKMCriterion ν → paperBKMInt ν → pStatementB ν

/-- `Corrected.clay_B_exact_of_corrected_route'`. -/
def formal_claim_clayBOfRoute : Prop :=
  ∀ ν : ℝ, PeriodicLocalExistence ν → PeriodicBKMCriterion ν → PeriodicBKMIntegrability ν →
    Clay_B_exact ν
/-- Paper: the same with local existence as a further hypothesis. -/
def paper_claim_clayBOfRoute : Prop :=
  ∀ ν : ℝ, 0 < ν → pLocalExistence ν → pBKMCriterion ν → paperBKMInt ν → pStatementB ν

/-! ### Bridges -/

theorem data_iff' (u₀ : VelocityField) : IsPeriodicSmoothInitialData u₀ ↔ pDatum u₀ :=
  TruthGate.data_iff u₀

theorem maximal_iff (ν : ℝ) (u₀ : VelocityField) (u : TimeDependentVelocity)
    (p : TimeDependentPressure) : IsPeriodicMaximalSolution ν u₀ u p ↔ pMaximal ν u₀ u p := by
  unfold IsPeriodicMaximalSolution pMaximal
  rw [TruthGate.tstar_eq]
  exact forall_congr' fun T => imp_congr_right fun _ => imp_congr_right fun _ =>
    TruthGate.solOn_iff ν u₀ T u p

theorem tstar_pos_iff (ν : ℝ) (u₀ : VelocityField) :
    (0 : EReal) < paperTstar ν u₀ ↔
      ∃ (T : ℝ) (u : TimeDependentVelocity) (p : TimeDependentPressure), paperSolOn ν u₀ T u p := by
  unfold paperTstar
  rw [lt_sSup_iff]
  constructor
  · rintro ⟨s, ⟨T, rfl, u, p, h⟩, -⟩
    exact ⟨T, u, p, h⟩
  · rintro ⟨T, u, p, h⟩
    exact ⟨(T : EReal), ⟨T, rfl, u, p, h⟩, EReal.coe_pos.2 h.1⟩

theorem loc_iff (ν : ℝ) : PeriodicLocalExistence ν ↔ (0 < ν → pLocalExistence ν) := by
  unfold PeriodicLocalExistence pLocalExistence
  constructor
  · intro h hν u₀ hd
    have := h hν u₀ ((data_iff' u₀).2 hd)
    rw [TruthGate.tstar_eq] at this
    exact (tstar_pos_iff ν u₀).1 this
  · intro h hν u₀ hd
    rw [TruthGate.tstar_eq]
    exact (tstar_pos_iff ν u₀).2 (h hν u₀ ((data_iff' u₀).1 hd))

theorem crit_iff (ν : ℝ) : PeriodicBKMCriterion ν ↔ (0 < ν → pBKMCriterion ν) := by
  unfold PeriodicBKMCriterion pBKMCriterion
  constructor
  · intro h hν u₀ hd u p hm T hT
    have := h hν u₀ ((data_iff' u₀).2 hd) u p ((maximal_iff ν u₀ u p).2 hm) T
      (by rw [TruthGate.tstar_eq]; exact hT)
    simpa only [TruthGate.supNorm_eq] using this
  · intro h hν u₀ hd u p hm T hT
    have := h hν u₀ ((data_iff' u₀).1 hd) u p ((maximal_iff ν u₀ u p).1 hm) T
      (by rw [← TruthGate.tstar_eq]; exact hT)
    simpa only [TruthGate.supNorm_eq] using this

theorem global_iff (ν : ℝ) : PeriodicGlobalLifespan ν ↔
    (0 < ν → ∀ u₀ : VelocityField, pDatum u₀ → paperTstar ν u₀ = ⊤) := by
  unfold PeriodicGlobalLifespan
  constructor
  · intro h hν u₀ hd
    rw [← TruthGate.tstar_eq]
    exact h hν u₀ ((data_iff' u₀).2 hd)
  · intro h hν u₀ hd
    rw [TruthGate.tstar_eq]
    exact h hν u₀ ((data_iff' u₀).1 hd)

theorem clayB_iff (ν : ℝ) : Clay_B_exact ν ↔ (0 < ν → pStatementB ν) := by
  constructor
  · intro h hν u₀ hd
    obtain ⟨u, p, hpu, hpp, hsu, hsp, hns, hdiv, h0⟩ := h hν u₀ ((data_iff' u₀).2 hd)
    refine ⟨u, p, hsu, hsp, ?_, hdiv, h0, ?_⟩
    · intro t ht x
      have := hns t ht x
      simp only [convective, laplacian, pressureGradient, add_zero] at this
      exact this
    · intro t ht x j
      exact ⟨(periodic_iff (u t)).1 (hpu t ht) x j, (periodic_iff (p t)).1 (hpp t ht) x j⟩
  · intro h hν u₀ hd
    obtain ⟨u, p, hsu, hsp, hns, hdiv, h0, hper⟩ := h hν u₀ ((data_iff' u₀).1 hd)
    refine ⟨u, p, fun t ht => (periodic_iff (u t)).2 fun x j => (hper t ht x j).1,
      fun t ht => (periodic_iff (p t)).2 fun x j => (hper t ht x j).2, hsu, hsp, ?_, hdiv, h0⟩
    intro t ht x
    simp only [convective, laplacian, pressureGradient, add_zero]
    exact hns t ht x

theorem coeff_eq (f : (Fin 3 → ℝ) → ℂ) (k : Fin 3 → ℤ) : cubeCoeff f k = pCoeff f k := by
  unfold cubeCoeff pCoeff
  congr 1
  funext x
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]

theorem DL_eq : ∀ (L : List (Fin 3)) (φ : T3 → ℝ), DL L φ = pD L φ
  | [], _ => rfl
  | a :: L, φ => by
      show pdR a (DL L φ) = fun y => fderiv ℝ (pD L φ) y (EuclideanSpace.single a 1)
      rw [DL_eq L φ]
      rfl

theorem term_eq (v : VelocityField) (i l : Fin 3) (L : List (Fin 3)) :
    cellI (fun y => DL L (fun y => v y i) y *
        (DL [] (fun y => v y l) y * DL L (pdR l (fun y => v y i)) y)) =
      pCube (fun y => pD L (fun z => v z i) y *
        (v y l * pD L (fun z => fderiv ℝ (fun w => v w i) z (EuclideanSpace.single l 1)) y)) := by
  simp only [DL_eq]
  rfl

/-! ### Correspondences -/

theorem intended_correspondence_localExistence :
    formal_claim_localExistence ↔ paper_claim_localExistence := by
  constructor
  · intro h ν hν
    exact (loc_iff ν).1 (h ν hν.le) hν
  · intro h ν _
    exact (loc_iff ν).2 (h ν)

theorem intended_correspondence_energyDifference :
    formal_claim_energyDifference ↔ paper_claim_energyDifference := by
  constructor
  · intro h ν hν u₀ T u v p q hu hv
    exact h ν hν u₀ T u v p q ((TruthGate.solOn_iff ν u₀ T u p).2 hu)
      ((TruthGate.solOn_iff ν u₀ T v q).2 hv)
  · intro h ν hν u₀ T u v p q hu hv
    exact h ν hν u₀ T u v p q ((TruthGate.solOn_iff ν u₀ T u p).1 hu)
      ((TruthGate.solOn_iff ν u₀ T v q).1 hv)

theorem intended_correspondence_uniqueness :
    formal_claim_uniqueness ↔ paper_claim_uniqueness := by
  constructor
  · intro h ν hν u₀ T u v p q hu hv
    exact h ν hν u₀ T u v p q ((TruthGate.solOn_iff ν u₀ T u p).2 hu)
      ((TruthGate.solOn_iff ν u₀ T v q).2 hv)
  · intro h ν hν u₀ T u v p q hu hv
    exact h ν hν u₀ T u v p q ((TruthGate.solOn_iff ν u₀ T u p).1 hu)
      ((TruthGate.solOn_iff ν u₀ T v q).1 hv)

theorem intended_correspondence_maximal : formal_claim_maximal ↔ paper_claim_maximal := by
  constructor
  · intro h ν hν u₀ hd
    obtain ⟨u, p, hm⟩ := h ν hν u₀ ((data_iff' u₀).2 hd)
    exact ⟨u, p, (maximal_iff ν u₀ u p).1 hm⟩
  · intro h ν hν u₀ hd
    obtain ⟨u, p, hm⟩ := h ν hν u₀ ((data_iff' u₀).1 hd)
    exact ⟨u, p, (maximal_iff ν u₀ u p).2 hm⟩

theorem intended_correspondence_parseval : formal_claim_parseval ↔ paper_claim_parseval := by
  constructor
  · intro h f g hf hg hfp hgp
    have := h f g hf hg hfp hgp
    simp only [coeff_eq] at this
    exact ⟨this.summable, this.tsum_eq⟩
  · intro h f g hf hg hfp hgp
    obtain ⟨hs, he⟩ := h f g hf hg hfp hgp
    simp only [coeff_eq]
    rw [← he]
    exact hs.hasSum

theorem intended_correspondence_topTerm : formal_claim_topTerm ↔ paper_claim_topTerm := by
  constructor
  · intro h v hv L
    have := h v ((data_iff' v).2 hv) L
    simpa only [term_eq] using this
  · intro h v hv L
    have := h v ((data_iff' v).1 hv) L
    simpa only [term_eq] using this

theorem intended_correspondence_bkmCriterion :
    formal_claim_bkmCriterion ↔ paper_claim_bkmCriterion := by
  constructor
  · intro h ν hν
    exact (crit_iff ν).1 (h ν) hν
  · intro h ν
    exact (crit_iff ν).2 (h ν)

theorem intended_correspondence_integrableBelow :
    formal_claim_integrableBelow ↔ paper_claim_integrableBelow := by
  constructor
  · intro h ν hν u₀ u p hm T hT
    have := h ν hν u₀ u p ((maximal_iff ν u₀ u p).2 hm) T (by rw [TruthGate.tstar_eq]; exact hT)
    simpa only [TruthGate.supNorm_eq] using this
  · intro h ν hν u₀ u p hm T hT
    have := h ν hν u₀ u p ((maximal_iff ν u₀ u p).1 hm) T (by rw [← TruthGate.tstar_eq]; exact hT)
    simpa only [TruthGate.supNorm_eq] using this

theorem intended_correspondence_bkmIffGlobal :
    formal_claim_bkmIffGlobal ↔ paper_claim_bkmIffGlobal := by
  constructor
  · intro h ν
    rw [← TruthGate.bkmInt_iff, ← global_iff]
    exact h ν
  · intro h ν
    rw [TruthGate.bkmInt_iff, global_iff]
    exact h ν

theorem intended_correspondence_clayBOfGlobal :
    formal_claim_clayBOfGlobal ↔ paper_claim_clayBOfGlobal := by
  constructor
  · intro h ν hν hg
    exact (clayB_iff ν).1 (h ν ((global_iff ν).2 fun _ => hg)) hν
  · intro h ν hg
    exact (clayB_iff ν).2 fun hν => h ν hν ((global_iff ν).1 hg hν)

theorem intended_correspondence_clayBOfBKM :
    formal_claim_clayBOfBKM ↔ paper_claim_clayBOfBKM := by
  constructor
  · intro h ν hν hc hi
    exact (clayB_iff ν).1 (h ν ((crit_iff ν).2 fun _ => hc) ((TruthGate.bkmInt_iff ν).2 hi)) hν
  · intro h ν hc hi
    exact (clayB_iff ν).2 fun hν => h ν hν ((crit_iff ν).1 hc hν) ((TruthGate.bkmInt_iff ν).1 hi)

theorem intended_correspondence_clayBOfRoute :
    formal_claim_clayBOfRoute ↔ paper_claim_clayBOfRoute := by
  constructor
  · intro h ν hν hl hc hi
    exact (clayB_iff ν).1 (h ν ((loc_iff ν).2 fun _ => hl) ((crit_iff ν).2 fun _ => hc)
      ((TruthGate.bkmInt_iff ν).2 hi)) hν
  · intro h ν hl hc hi
    exact (clayB_iff ν).2 fun hν => h ν hν ((loc_iff ν).1 hl hν) ((crit_iff ν).1 hc hν)
      ((TruthGate.bkmInt_iff ν).1 hi)
-- TRUTH-GATE LOCK END

/-! ### The repository theorems prove the formal claims; the paper claims follow by transport -/

theorem formal_claim_holds_localExistence : formal_claim_localExistence :=
  fun _ hν => periodicLocalExistence_of_nonneg hν
theorem paper_claim_holds_localExistence : paper_claim_localExistence :=
  intended_correspondence_localExistence.mp formal_claim_holds_localExistence

theorem formal_claim_holds_energyDifference : formal_claim_energyDifference :=
  fun _ hν => Corrected.periodicEnergyDifferenceEstimate hν
theorem paper_claim_holds_energyDifference : paper_claim_energyDifference :=
  intended_correspondence_energyDifference.mp formal_claim_holds_energyDifference

theorem formal_claim_holds_uniqueness : formal_claim_uniqueness :=
  fun ν hν => Corrected.periodicVelocityUniqueness_of_energy ν
    (Corrected.periodicEnergyDifferenceEstimate hν)
theorem paper_claim_holds_uniqueness : paper_claim_uniqueness :=
  intended_correspondence_uniqueness.mp formal_claim_holds_uniqueness

theorem formal_claim_holds_maximal : formal_claim_maximal :=
  fun ν hν => Corrected.periodicMaximalSolution_of_uniqueness
    (Corrected.periodicVelocityUniqueness_of_energy ν
      (Corrected.periodicEnergyDifferenceEstimate hν.le)) hν
theorem paper_claim_holds_maximal : paper_claim_maximal :=
  intended_correspondence_maximal.mp formal_claim_holds_maximal

theorem formal_claim_holds_parseval : formal_claim_parseval :=
  fun _ _ hf hg hfp hgp => hasSum_prod_cubeCoeff hf hg hfp hgp
theorem paper_claim_holds_parseval : paper_claim_parseval :=
  intended_correspondence_parseval.mp formal_claim_holds_parseval

theorem formal_claim_holds_topTerm : formal_claim_topTerm :=
  fun _ hv L => top_term_zero hv L
theorem paper_claim_holds_topTerm : paper_claim_topTerm :=
  intended_correspondence_topTerm.mp formal_claim_holds_topTerm

theorem formal_claim_holds_bkmCriterion : formal_claim_bkmCriterion :=
  fun ν => periodicBKMCriterion ν
theorem paper_claim_holds_bkmCriterion : paper_claim_bkmCriterion :=
  intended_correspondence_bkmCriterion.mp formal_claim_holds_bkmCriterion

theorem formal_claim_holds_integrableBelow : formal_claim_integrableBelow :=
  fun _ hν _ _ _ hm _ hT => integrableOn_vorticity_of_lt_tstar hν hm hT
theorem paper_claim_holds_integrableBelow : paper_claim_integrableBelow :=
  intended_correspondence_integrableBelow.mp formal_claim_holds_integrableBelow

theorem formal_claim_holds_bkmIffGlobal : formal_claim_bkmIffGlobal :=
  fun ν => periodicBKMIntegrability_iff_globalLifespan ν
theorem paper_claim_holds_bkmIffGlobal : paper_claim_bkmIffGlobal :=
  intended_correspondence_bkmIffGlobal.mp formal_claim_holds_bkmIffGlobal

theorem formal_claim_holds_clayBOfGlobal : formal_claim_clayBOfGlobal :=
  fun ν h => clay_B_exact_of_globalLifespan ν h
theorem paper_claim_holds_clayBOfGlobal : paper_claim_clayBOfGlobal :=
  intended_correspondence_clayBOfGlobal.mp formal_claim_holds_clayBOfGlobal

theorem formal_claim_holds_clayBOfBKM : formal_claim_clayBOfBKM :=
  fun ν hc hi => clay_B_exact_of_bkm ν hc hi
theorem paper_claim_holds_clayBOfBKM : paper_claim_clayBOfBKM :=
  intended_correspondence_clayBOfBKM.mp formal_claim_holds_clayBOfBKM

theorem formal_claim_holds_clayBOfRoute : formal_claim_clayBOfRoute :=
  fun ν hl hc hi => Corrected.clay_B_exact_of_corrected_route' ν hl hc hi
theorem paper_claim_holds_clayBOfRoute : paper_claim_clayBOfRoute :=
  intended_correspondence_clayBOfRoute.mp formal_claim_holds_clayBOfRoute

end TruthGatePaper
