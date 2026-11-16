/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import PeriodicNSContinuation.BKMFinal

/-!
# Truth Gate: semantics lock (see `TRUTH_GATE.md`)

PAPER_PATH: paper/periodic-ns-classical-continuation.tex
PAPER_SECTION: Section "Status" (conditional item: Statement (B) conditional on PeriodicBKMIntegrability), with Section "Modelling of the torus" (sec:model) and the hypothesis PeriodicBKMIntegrability of Section "Conditional results"
PAPER_SHA256: 4aeaa07d97e2a5c7700405c79d602ba2985234ccc5b76ba8854fe33958837f48

Locked paper claim, quoted verbatim (the claim, the model it is read in, and the hypothesis):

PAPER_QUOTE_BEGIN
\item \textbf{Conditional:} Statement~(B) is proven conditionally on \lean{PeriodicBKMIntegrability} (\lean{clay_B_exact_of_integrability}).
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
In the Lean development the torus is not a quotient type. The carrier \lean{T3} is \lean{EuclideanSpace ℝ (Fin 3)}, i.e.\ $\mathbb{R}^3$; a field on $\TT$ is a field on $\mathbb{R}^3$ satisfying \lean{IsZ3Periodic} (invariance under translation by $\mathbb{Z}^3$), and every spatial integral is taken over one unit cell $[0,1]^3$ (\lean{torusIntegral}). \lean{IsPeriodicSmoothSolution} (\file{FeffermanStatements.lean}) requires a smooth $\mathbb{Z}^3$-periodic pair $(u,p)$ with
\[\partial_t u+(u\cdot\nabla)u=\nu\Delta u-\nabla p,\qquad \Div u=0,\qquad u(0)=u_0 .\]
This is a faithful encoding of the periodic problem; every Clay- and BKM-type statement in this paper is to be read in this model.
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
From the dependency \file{fefferman-clay-navier-stokes}: $\int_0^T\norm{\omega}_{L^\infty}\dd t<\infty$ on every finite interval of existence.
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
We prove this hypothesis is equivalent to global existence of smooth solutions for every smooth periodic initial field.
PAPER_QUOTE_END

Reading of the paper's terms:
* Statement (B) is Fefferman's periodic statement, read in the paper's model (sec:model): for
  `ν > 0` and every smooth, divergence-free, `ℤ³`-periodic initial field `u₀` on `ℝ³`
  (Fefferman's data for (B); `f ≡ 0`), there is a pair `(u, p)`, smooth on `[0,∞) × ℝ³`,
  periodic under the unit shifts `x ↦ x + eⱼ` (Fefferman Eq. (8)/(10)) for `t ≥ 0`, with
  `∂ₜu + (u·∇)u = νΔu - ∇p` and `div u = 0` for `t ≥ 0` and `u(0) = u₀`;
* `∂ₜu` at `t ≥ 0` is the derivative within `[0,∞)` (one-sided at `t = 0`); `(u·∇)u` is
  `Du(x)(u(x))`; `Δu = Σᵢ ∂ᵢ∂ᵢu`; `∇p` is Mathlib's `gradient`; `div u = Σᵢ ∂ᵢuᵢ`;
* the hypothesis is the paper's named open Prop `PeriodicBKMIntegrability ν` (`∫₀ᵀ ‖ω‖_∞ < ∞` along
  the maximal solution); it is an assumption of the claim and is kept as the named Prop. It is
  OPEN: nothing here proves it, so nothing here proves Statement (B).

`formal_claim` is the statement of `PeriodicNSContinuation.clay_B_exact_of_integrability`, phrased
with `Clay_B_exact`, `IsPeriodicSmoothInitialData`, `IsPeriodicSmoothSolution` and `IsZ3Periodic`
(full lattice periodicity). `paper_claim` spells Statement (B) out with Mathlib's `fderiv`,
`derivWithin` and `gradient` and the unit-shift form of periodicity. The correspondence uses the
equivalence of lattice and unit-shift periodicity and unfolds the repository's operators.

Scope: CONDITIONAL on the open `PeriodicBKMIntegrability`. This does not prove Statement (B), does
not prove global regularity, and the Clay Millennium problem remains open.
-/

namespace TruthGate

open scoped ContDiff Gradient
open FeffermanClayNS NavierStokes3D

-- TRUTH-GATE LOCK BEGIN
/-- The repository's statement (`clay_B_exact_of_integrability`). -/
def formal_claim : Prop :=
  ∀ ν : ℝ, PeriodicBKMIntegrability ν → Clay_B_exact ν

/-- Paper: Statement (B) holds conditionally on `PeriodicBKMIntegrability`, spelled out. -/
def paper_claim : Prop :=
  ∀ ν : ℝ, 0 < ν → PeriodicBKMIntegrability ν →
    ∀ u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      ContDiff ℝ (⊤ : ℕ∞) u₀ →
      (∀ x, ∑ i : Fin 3, fderiv ℝ (fun y => u₀ y i) x (EuclideanSpace.single i 1) = 0) →
      (∀ x (j : Fin 3), u₀ (x + EuclideanSpace.single j 1) = u₀ x) →
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

theorem periodic_iff {α : Type*} (g : T3 → α) :
    IsZ3Periodic g ↔ ∀ x (j : Fin 3), g (x + EuclideanSpace.single j 1) = g x := by
  rw [isZ3Periodic_iff_unit_shifts]
  rfl

/-- The fixed correspondence between the formal statement and the paper's claim. -/
theorem intended_correspondence : formal_claim ↔ paper_claim := by
  constructor
  · intro h ν hν hint u₀ hs hd hp
    obtain ⟨u, p, hpu, hpp, hsu, hsp, hns, hdiv, h0⟩ :=
      h ν hint hν u₀ ⟨hs, hd, (periodic_iff u₀).2 hp⟩
    refine ⟨u, p, hsu, hsp, ?_, hdiv, h0, ?_⟩
    · intro t ht x
      have := hns t ht x
      simp only [convective, laplacian, pressureGradient, add_zero] at this
      exact this
    · intro t ht x j
      exact ⟨(periodic_iff (u t)).1 (hpu t ht) x j, (periodic_iff (p t)).1 (hpp t ht) x j⟩
  · rintro h ν hint hν u₀ ⟨hs, hd, hp⟩
    obtain ⟨u, p, hsu, hsp, hns, hdiv, h0, hper⟩ := h ν hν hint u₀ hs hd ((periodic_iff u₀).1 hp)
    refine ⟨u, p, fun t ht => (periodic_iff (u t)).2 fun x j => (hper t ht x j).1,
      fun t ht => (periodic_iff (p t)).2 fun x j => (hper t ht x j).2, hsu, hsp, ?_, hdiv, h0⟩
    intro t ht x
    simp only [convective, laplacian, pressureGradient, add_zero]
    exact hns t ht x
-- TRUTH-GATE LOCK END

/-- The repository's theorem proves `formal_claim`. -/
theorem formal_claim_holds : formal_claim := by
  intro ν hint
  exact PeriodicNSContinuation.clay_B_exact_of_integrability ν hint

/-- The paper's claim, transported across the correspondence. -/
theorem paper_claim_holds : paper_claim :=
  intended_correspondence.mp formal_claim_holds

end TruthGate
