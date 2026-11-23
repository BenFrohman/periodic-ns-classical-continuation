/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import PeriodicNSContinuation.IntegrabilityAttack

/-!
# Truth Gate: semantics lock (see `TRUTH_GATE.md`)

PAPER_PATH: paper/periodic-ns-classical-continuation.tex
PAPER_SECTION: Section "Status" (conditional item: Statement (B) conditional on PeriodicBKMIntegrability), with Section "Modelling of the torus" (sec:model) and the hypothesis PeriodicBKMIntegrability of Section "Conditional results"
PAPER_SHA256: 947e4e31f881b05bb34ac8a1b9d7b2736812f4e0e24b425c3aa942c9d57de827

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
From the dependency \file{fefferman-clay-navier-stokes}. For $\nu>0$ and initial data $u_0$, let $\Tstar(u_0)\in[-\infty,\infty]$ be the supremum of the real $T$ for which some pair $(u,p)$ is a smooth periodic solution on $[0,T]$ with data $u_0$: $T>0$; $u(t)$ and $p(t)$ are $\mathbb{Z}^3$-periodic for $t\in[0,T]$; $u$ and $p$ are $C^\infty$ on $[0,T]\times\mathbb{R}^3$; $\partial_t u+(u\cdot\nabla)u=\nu\Delta u-\nabla p$ and $\Div u=0$ on $[0,T]\times\mathbb{R}^3$, with $\partial_t$ the derivative within $[0,T]$; and $u(0)=u_0$. The hypothesis states: for every smooth, divergence-free, $\mathbb{Z}^3$-periodic $u_0$ and every pair $(u,p)$ that is a smooth periodic solution on $[0,T]$ for every real $T$ with $0<T<\Tstar(u_0)$, the function $t\mapsto\norm{\omega(t)}_{L^\infty}=\sup_x\abs{(\nabla\times u(t))(x)}$ is integrable on $[0,T]$ for \emph{every} real $T$. When $\Tstar(u_0)<\infty$ this includes $T=\Tstar(u_0)$ and times after it, where the solution property places no constraint on $u$; so the hypothesis is not the bounded-interval condition $T<\Tstar(u_0)$.
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
* the hypothesis is written out from the paper's sentence (`paperBKMInt`, with `paperSolOn`,
  `paperTstar`, `paperCurl`), not reused as the repository Prop `PeriodicBKMIntegrability`:
  `‖ω(t)‖_∞` is `⨆ x, ‖(∇ × u(t))(x)‖`, integrability is Mathlib's `IntegrableOn` on `[0, T]` for
  every real `T`, and `T*` is `sSup` in `EReal`. It is OPEN: nothing here proves it, so nothing here
  proves Statement (B);
* "equivalent to global existence ... for every smooth periodic initial field" is
  `paperBKMInt ν ↔ (0 < ν → ∀ u₀ smooth periodic divergence-free, T*(u₀) = ⊤)`.

`formal_claim` is the conjunction of the statements of
`PeriodicNSContinuation.clay_B_exact_of_integrability` and
`PeriodicNSContinuation.periodicBKMIntegrability_iff_globalLifespan`, phrased
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
/-- The repository's statements: `clay_B_exact_of_integrability` and
`periodicBKMIntegrability_iff_globalLifespan`. -/
def formal_claim : Prop :=
  (∀ ν : ℝ, PeriodicBKMIntegrability ν → Clay_B_exact ν) ∧
  (∀ ν : ℝ, PeriodicBKMIntegrability ν ↔ PeriodicNSContinuation.PeriodicGlobalLifespan ν)

/-- Paper (Section "Conditional results"): `(u, p)` is a smooth periodic solution on `[0, T]` with
data `u₀`, written out from the paper's list (unit-shift periodicity, `C^∞` on `[0,T] × ℝ³`, the
momentum equation with `∂ₜ` the derivative within `[0,T]`, `div u = 0`, `u(0) = u₀`). -/
def paperSolOn (ν : ℝ) (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (T : ℝ)
    (u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (p : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ) : Prop :=
  0 < T ∧
  (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x (j : Fin 3), u t (x + EuclideanSpace.single j 1) = u t x) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x (j : Fin 3), p t (x + EuclideanSpace.single j 1) = p t x) ∧
  ContDiffOn ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => u q.1 q.2) (Set.Icc (0 : ℝ) T ×ˢ Set.univ) ∧
  ContDiffOn ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => p q.1 q.2) (Set.Icc (0 : ℝ) T ×ˢ Set.univ) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
    derivWithin (fun s => u s x) (Set.Icc (0 : ℝ) T) t + fderiv ℝ (u t) x (u t x) =
      ν • ∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ (u t) y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1) - ∇ (p t) x) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
    ∑ i : Fin 3, fderiv ℝ (fun y => u t y i) x (EuclideanSpace.single i 1) = 0) ∧
  (∀ x, u 0 x = u₀ x)

/-- Paper: `T*(u₀)`, the supremum in `[-∞, ∞]` of the real `T` with a smooth periodic solution on
`[0, T]`. -/
noncomputable def paperTstar (ν : ℝ) (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) :
    EReal :=
  sSup {s : EReal | ∃ T : ℝ, s = (T : EReal) ∧ ∃ u p, paperSolOn ν u₀ T u p}

/-- Paper: `∇ × v`, componentwise `(∂₂v₃ - ∂₃v₂, ∂₃v₁ - ∂₁v₃, ∂₁v₂ - ∂₂v₁)` (indices `0,1,2`). -/
noncomputable def paperCurl (v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single 0 (fderiv ℝ (fun y => v y 2) x (EuclideanSpace.single 1 1) -
      fderiv ℝ (fun y => v y 1) x (EuclideanSpace.single 2 1)) +
    EuclideanSpace.single 1 (fderiv ℝ (fun y => v y 0) x (EuclideanSpace.single 2 1) -
      fderiv ℝ (fun y => v y 2) x (EuclideanSpace.single 0 1)) +
    EuclideanSpace.single 2 (fderiv ℝ (fun y => v y 1) x (EuclideanSpace.single 0 1) -
      fderiv ℝ (fun y => v y 0) x (EuclideanSpace.single 1 1))

/-- Paper: the hypothesis `PeriodicBKMIntegrability ν`, written out from the paper's sentence:
for `ν > 0`, smooth divergence-free unit-shift-periodic `u₀`, and every `(u, p)` that is a smooth
periodic solution on `[0, T]` for every real `0 < T < T*(u₀)`, `t ↦ sup_x |∇ × u(t)|` is integrable
on `[0, T]` for every real `T`. -/
def paperBKMInt (ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
    ContDiff ℝ (⊤ : ℕ∞) u₀ →
    (∀ x, ∑ i : Fin 3, fderiv ℝ (fun y => u₀ y i) x (EuclideanSpace.single i 1) = 0) →
    (∀ x (j : Fin 3), u₀ (x + EuclideanSpace.single j 1) = u₀ x) →
    ∀ (u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (p : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ),
      (∀ T : ℝ, 0 < T → (T : EReal) < paperTstar ν u₀ → paperSolOn ν u₀ T u p) →
      ∀ T : ℝ, MeasureTheory.IntegrableOn (fun t => ⨆ x, ‖paperCurl (u t) x‖) (Set.Icc 0 T)

/-- Paper: Statement (B) holds conditionally on the hypothesis, spelled out; and the hypothesis is
equivalent to global existence (`T*(u₀) = ∞` for every smooth periodic initial field). -/
def paper_claim : Prop :=
  (∀ ν : ℝ, 0 < ν → paperBKMInt ν →
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
          u t (x + EuclideanSpace.single j 1) = u t x ∧ p t (x + EuclideanSpace.single j 1) = p t x)) ∧
  (∀ ν : ℝ, paperBKMInt ν ↔
    (0 < ν → ∀ u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      ContDiff ℝ (⊤ : ℕ∞) u₀ →
      (∀ x, ∑ i : Fin 3, fderiv ℝ (fun y => u₀ y i) x (EuclideanSpace.single i 1) = 0) →
      (∀ x (j : Fin 3), u₀ (x + EuclideanSpace.single j 1) = u₀ x) →
      paperTstar ν u₀ = ⊤))

theorem periodic_iff {α : Type*} (g : T3 → α) :
    IsZ3Periodic g ↔ ∀ x (j : Fin 3), g (x + EuclideanSpace.single j 1) = g x := by
  rw [isZ3Periodic_iff_unit_shifts]
  rfl

theorem solOn_iff (ν : ℝ) (u₀ : VelocityField) (T : ℝ) (u : TimeDependentVelocity)
    (p : TimeDependentPressure) :
    IsPeriodicSmoothSolutionOn ν u₀ (fun _ _ => 0) T u p ↔ paperSolOn ν u₀ T u p := by
  unfold IsPeriodicSmoothSolutionOn paperSolOn
  simp only [periodic_iff, convective, laplacian, pressureGradient, add_zero, div]

theorem tstar_eq (ν : ℝ) (u₀ : VelocityField) : periodicTstar ν u₀ = paperTstar ν u₀ := by
  unfold periodicTstar periodicExistenceTimes paperTstar
  simp only [solOn_iff]

theorem supNorm_eq (v : VelocityField) :
    vorticity_sup_norm (vorticity v) = ⨆ x, ‖paperCurl v x‖ := by
  unfold vorticity_sup_norm vorticity curl paperCurl directionalCoord
  rfl

theorem data_iff (u₀ : VelocityField) :
    IsPeriodicSmoothInitialData u₀ ↔
      (ContDiff ℝ (⊤ : ℕ∞) u₀ ∧
        (∀ x, ∑ i : Fin 3, fderiv ℝ (fun y => u₀ y i) x (EuclideanSpace.single i 1) = 0) ∧
        (∀ x (j : Fin 3), u₀ (x + EuclideanSpace.single j 1) = u₀ x)) := by
  unfold IsPeriodicSmoothInitialData
  rw [periodic_iff]
  rfl

theorem bkmInt_iff (ν : ℝ) : PeriodicBKMIntegrability ν ↔ paperBKMInt ν := by
  unfold PeriodicBKMIntegrability IsPeriodicMaximalSolution paperBKMInt
  constructor
  · intro h hν u₀ hs hd hp u p hmax T
    have := h hν u₀ ((data_iff u₀).2 ⟨hs, hd, hp⟩) u p
      (fun T hT hlt => (solOn_iff ν u₀ T u p).2 (hmax T hT (by rwa [← tstar_eq]))) T
    simpa only [supNorm_eq] using this
  · intro h hν u₀ hdata u p hmax T
    obtain ⟨hs, hd, hp⟩ := (data_iff u₀).1 hdata
    have := h hν u₀ hs hd hp u p
      (fun T hT hlt => (solOn_iff ν u₀ T u p).1 (hmax T hT (by rwa [tstar_eq]))) T
    simpa only [supNorm_eq] using this

/-- The fixed correspondence between the formal statement and the paper's claim. -/
theorem intended_correspondence : formal_claim ↔ paper_claim := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro ν hν hint u₀ hs hd hp
      obtain ⟨u, p, hpu, hpp, hsu, hsp, hns, hdiv, h0⟩ :=
        h1 ν ((bkmInt_iff ν).2 hint) hν u₀ ⟨hs, hd, (periodic_iff u₀).2 hp⟩
      refine ⟨u, p, hsu, hsp, ?_, hdiv, h0, ?_⟩
      · intro t ht x
        have := hns t ht x
        simp only [convective, laplacian, pressureGradient, add_zero] at this
        exact this
      · intro t ht x j
        exact ⟨(periodic_iff (u t)).1 (hpu t ht) x j, (periodic_iff (p t)).1 (hpp t ht) x j⟩
    · intro ν
      rw [← bkmInt_iff, h2 ν]
      unfold PeriodicNSContinuation.PeriodicGlobalLifespan
      simp only [data_iff, tstar_eq, and_imp]
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rintro ν hint hν u₀ ⟨hs, hd, hp⟩
      obtain ⟨u, p, hsu, hsp, hns, hdiv, h0, hper⟩ :=
        h1 ν hν ((bkmInt_iff ν).1 hint) u₀ hs hd ((periodic_iff u₀).1 hp)
      refine ⟨u, p, fun t ht => (periodic_iff (u t)).2 fun x j => (hper t ht x j).1,
        fun t ht => (periodic_iff (p t)).2 fun x j => (hper t ht x j).2, hsu, hsp, ?_, hdiv, h0⟩
      intro t ht x
      simp only [convective, laplacian, pressureGradient, add_zero]
      exact hns t ht x
    · intro ν
      rw [bkmInt_iff, h2 ν]
      unfold PeriodicNSContinuation.PeriodicGlobalLifespan
      simp only [data_iff, tstar_eq, and_imp]
-- TRUTH-GATE LOCK END

/-- The repository's theorem proves `formal_claim`. -/
theorem formal_claim_holds : formal_claim :=
  ⟨fun ν hint => PeriodicNSContinuation.clay_B_exact_of_integrability ν hint,
    fun ν => PeriodicNSContinuation.periodicBKMIntegrability_iff_globalLifespan ν⟩

/-- The paper's claim, transported across the correspondence. -/
theorem paper_claim_holds : paper_claim :=
  intended_correspondence.mp formal_claim_holds

end TruthGate
