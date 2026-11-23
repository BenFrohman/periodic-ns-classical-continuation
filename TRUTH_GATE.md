# TRUTH GATE — the GOD gate. Read this first.

Author: Benjamin Stanley Frohman. This file is the root instruction for every person and every
automated agent (every bot) that touches this repository. Load it before any other file.

**Only truth and honest, kernel-proved theorems pass this gate. Nothing from this repository is
published, released, deposited on Zenodo, cited or claimed unless the `truth-gate` check is green
on the exact commit being cited.** That is why it is the GOD gate: it sits above every other
check, and no other green check can stand in for it.

## The issue this gate fixes

A paper states its claim in English. Lean can only prove `formal_claim ↔ paper_claim` once
`paper_claim` is itself written in Lean. If `paper_claim` were simply *defined to be*
`formal_claim` (or an alias of it, or something that unfolds to it), the theorem
`intended_correspondence` would be `Iff.rfl`: it would be empty and prove nothing about the
paper. A green certificate could then "certify" a statement different from the one the paper
makes (drift), whether by accident or by an injected instruction.

## The fix rule (binding, permanent)

1. `paper_claim` is an **independent Lean transcription of the paper's exact claim**, written in
   the paper's own terms, with every hypothesis the paper states. The verbatim English quote,
   the paper path, its sha256 and the section are recorded in the doc comment of
   `Semantics.lean` **and** in this file (below).
2. `paper_claim` must **not** be defined as, reference, or trivially alias `formal_claim`.
3. `intended_correspondence : formal_claim ↔ paper_claim` must have a **substantive proof**. It
   may not be `Iff.rfl`, `rfl`, `exact Iff.rfl` or similar, and it may not use the main theorem
   (it is a statement-level equivalence, not "both sides happen to be provable").
4. `formal_claim` is exactly the statement of the repository's main theorem, and
   `paper_claim_holds` is the main theorem transported across the correspondence.
5. Only `propext`, `Classical.choice` and `Quot.sound`. No `sorry`, `admit`, `native_decide` or
   new `axiom` anywhere outside the draft directories in `TRUTH_GATE.lock`.
6. If the paper's English claim cannot be faithfully transcribed, or is not what Lean proves,
   the gate stays **red** and the mismatch is reported. Never patch over it: never weaken
   `paper_claim`, drop a hypothesis, or redefine it to match the formal side. If the
   formalization drifted, rewrite the formalization so it transports across the lock again.
7. Open problems stay hypotheses. No Millennium Prize problem is claimed solved; the gate only
   ensures the certificate proves precisely the locked claim and nothing else.
8. The locked region of `Semantics.lean`, the quote and `TRUTH_GATE.lock` change only with the
   author's explicit sign-off, as a PR that says "new lock" in its title.
9. Commits are authored by Benjamin Stanley Frohman only, with no AI co-author trailers. No
   force-push and no history rewriting.

## What `scripts/verify-lock.sh` checks mechanically

* `lake build` succeeds, with no `sorry` warning outside the draft directories;
* no `sorry` / `admit` / `native_decide` / `axiom` token outside the draft directories
  (comments and strings excluded);
* `Semantics.lean` has `PAPER_PATH`, `PAPER_SHA256`, `PAPER_SECTION` and a verbatim
  `PAPER_QUOTE`; the hash matches the paper file and the quote occurs in it; this file carries
  the same path, hash and quote;
* the lock region hash matches `TRUTH_GATE.lock`;
* `paper_claim`'s body does not mention `formal_claim`; the correspondence is not proved by
  `Iff.rfl`/`rfl`;
* in Lean: the bodies of `formal_claim` and `paper_claim` differ, the two are not
  definitionally equal, the correspondence proof does not reach the main theorem, the main
  theorem's statement is `formal_claim`, `paper_claim_holds` goes through the correspondence,
  and `#print axioms` shows only the three standard axioms.

What it cannot check: whether the transcription is the right reading of the English. That
reading is fixed once, in writing, below and in `Semantics.lean`, and is the author's sign-off.

## Running the gate locally

```
lake exe cache get
bash scripts/verify-lock.sh
```

Reports are written to `truth-gate-report/`.

## Failure classes (what a red Truth Gate means)

A red Truth Gate is not automatically a math failure. Since 2026-11-17, `scripts/verify-lock.sh`
runs every phase even after one fails. `scripts/truth_gate_classify.py` then sorts each failure
into exactly one class and prints a `TRUTH GATE VERDICT` block at the end of the log. The block
also goes to the job summary and to `truth-gate-report/classification.json`.

This exists because of frohmanian-tether-sdiff PR #13 (run 44039231121). That PR changed only CI,
but its merge ref was built on a main whose lock still had the old `paper_claim` form. The gate
printed `TRUTH GATE FAIL: this lock is NOT certifying` and `TRUTH GATE STATIC FAIL`, which read like
a proof failure, though every kernel check was green.

| Class | Raised by | What the verdict prints | What fixes it |
|---|---|---|---|
| **KERNEL/PROOF** | `lake build` fails; `sorry`/`admit`/`native_decide`/`axiom` outside the draft dirs; nonstandard axioms; a missing or ill-typed locked declaration; `intended_correspondence` fails to check | `KERNEL/PROOF FAILURE (a proof does not check)` and `This is a proof failure`, with the failing lines | Fix the proof. **This is the only class ever described as a proof failure.** |
| **LOCK-FORM** | `paper_claim` reuses a repository Prop or definition; a vacuous alias of `formal_claim`; an `rfl` correspondence; a partial lock; a lock marked `"certifying": false`; an edited lock region; missing `PAPER_*` fields | `LOCK-FORM: lock wording/form problem, not a math failure`, each offending identifier with `file:line` in the Semantics file and the `file:line` of its repository declaration, then the independent transcription that is required | Rewrite the paper side from the paper's own definition, in the paper's symbols, and prove `intended_correspondence` with real reasoning. A new lock needs the author's sign-off. |
| **PAPER-HASH** | the paper's sha256 differs from the lock | `PAPER-HASH: the paper changed after the lock (not a math failure)`, the commit whose bytes match the lock, every changed line, whether only copyright/license/attribution lines changed, and whether the locked quote is still verbatim | If the edit is intended, update `paper_sha256` in `TRUTH_GATE.lock`, the `PAPER_SHA256:` line in the Semantics file and the hash in this file, all in one commit. If the quote changed, that is a statement change and needs sign-off. |
| **STALE-BASE** | a PR's merge ref was built on an older main, and main has since changed the lock, a Semantics file, a paper or a gate script | `STALE-BASE: branch is behind main's lock; update branch (not a math failure)` | The workflow re-merges the PR head onto the current main and judges that merge, which is what would actually land. It goes red only if that merge conflicts, and then it says to update the branch. |

Two more labels can appear in the verdict:

* **`[INHERITED]`** appears when the PR touches no lock, vocabulary, Semantics or paper file but a
  LOCK-FORM or PAPER-HASH failure remains. The failure comes from main, so it has to be fixed on
  main.
* **`UNCLASSIFIED`** appears when a checker crashed or printed a message no rule recognises. It is
  shown verbatim and is never presumed to be a math failure.

The last line always states the classes, for example
`VERDICT: FAIL (LOCK-FORM). Kernel checks passed: no math was found false.`

### Lock-form lint (runs on every PR, no Lean needed)

The `lock-form-lint` job in `.github/workflows/truth-gate.yml` runs
`python3 scripts/truth_gate_classify.py lint --fetch-deps`. It collects every declaration in
`lean_roots` and in the author's own Lake dependencies (every non-Mathlib package in
`lake-manifest.json`), then reads `paper_claim` and any paper-side helper defined in the Semantics
file. It rejects:

1. any Prop that is a whole hypothesis or the conclusion of `formal_claim` (for example the old
   sdiff form `(∀ ν > 0, PeriodicTetherClosingBound ν) → …`). This is never allowed, with or without
   a vocabulary entry;
2. any other repository name that is not listed, with a reason, in `TRUTH_GATE.vocabulary.json`
   (basic notions such as the velocity-field type);
3. any name in `paper_forbidden_names`, and any mention of `formal_claim`.

`TRUTH_GATE.vocabulary.json` is lint configuration. It cannot change the locked claim, because the
lock region hash still pins `paper_claim`. For an existing author-approved lock, it records only the
basic names that the approved claim already uses. Any new name on the paper side goes into the
new-lock PR together with the author's sign-off.

### Tests

`scripts/tests/test_truth_gate_classify.py` has one throw-away fixture repository per class:

* KERNEL/PROOF: build error, sorry, nonstandard axioms;
* LOCK-FORM: named hypothesis Prop, unlisted repository name, alias, non-certifying,
  partial lock, vacuous lock;
* PAPER-HASH: copyright-only change, and a change to the quote;
* STALE-BASE: re-merge onto the current main, and a merge conflict;
* `[INHERITED]` label.

The `lock-form-lint` job runs them on every PR:

```
python3 -m unittest discover -s scripts/tests -p 'test_truth_gate_classify.py' -v
```

## The locked claim of this repository

* Paper: `paper/periodic-ns-classical-continuation.tex`
* sha256: `ae41820715ddf983ece536e21a78887ea99e6b70fda50fb8f5d48bee0f58b422`
* Section: Section "Status" (conditional item: Statement (B) conditional on PeriodicBKMIntegrability), with Section "Modelling of the torus" (sec:model) and the hypothesis PeriodicBKMIntegrability of Section "Conditional results"
* Main theorem(s): `PeriodicNSContinuation.clay_B_exact_of_integrability`
* Lock file: `TRUTH_GATE.lock`; semantics: `PeriodicNSContinuation/Semantics.lean`

Verbatim quote:

```
\item \textbf{Conditional:} Statement~(B) is proven conditionally on \lean{PeriodicBKMIntegrability} (\lean{clay_B_exact_of_integrability}).

In the Lean development the torus is not a quotient type. The carrier \lean{T3} is \lean{EuclideanSpace ℝ (Fin 3)}, i.e.\ $\mathbb{R}^3$; a field on $\TT$ is a field on $\mathbb{R}^3$ satisfying \lean{IsZ3Periodic} (invariance under translation by $\mathbb{Z}^3$), and every spatial integral is taken over one unit cell $[0,1]^3$ (\lean{torusIntegral}). \lean{IsPeriodicSmoothSolution} (\file{FeffermanStatements.lean}) requires a smooth $\mathbb{Z}^3$-periodic pair $(u,p)$ with
\[\partial_t u+(u\cdot\nabla)u=\nu\Delta u-\nabla p,\qquad \Div u=0,\qquad u(0)=u_0 .\]
This is a faithful encoding of the periodic problem; every Clay- and BKM-type statement in this paper is to be read in this model.

From the dependency \file{fefferman-clay-navier-stokes}. Let $\nu>0$. A pair $(u,p)$ is a smooth periodic solution on $[0,T]$ with data $u_0$ if $T>0$; $u(t)$ and $p(t)$ are $\mathbb{Z}^3$-periodic for $t\in[0,T]$; $u$ and $p$ are $C^\infty$ on $[0,T]\times\mathbb{R}^3$; $\partial_t u+(u\cdot\nabla)u=\nu\Delta u-\nabla p$ and $\Div u=0$ on $[0,T]\times\mathbb{R}^3$, with $\partial_t$ the derivative within $[0,T]$; and $u(0)=u_0$. Let $\Tstar(u_0)\in[-\infty,\infty]$ be the supremum of the real $T$ for which such a pair exists. The hypothesis states: for every smooth, divergence-free, $\mathbb{Z}^3$-periodic $u_0$ and every pair $(u,p)$ that is a smooth periodic solution on $[0,T]$ with data $u_0$ for every real $T$ with $0<T<\Tstar(u_0)$, the function $t\mapsto\norm{\omega(t)}_{L^\infty}=\sup_{x\in\mathbb{R}^3}\abs{(\nabla\times u(t))(x)}$ is integrable on $[0,T]$ (\lean{IntegrableOn}) for every real $T$; in particular $\int_0^T\norm{\omega(t)}_{L^\infty}\dd t<\infty$ for every real $T$. The supremum is the real supremum \lean{iSup}, which Lean sets to $0$ when the set is unbounded. When $\Tstar(u_0)<\infty$ the condition includes every $T\ge\Tstar(u_0)$, where the solution property places no constraint on $u$; it is not only a condition on intervals of existence.

We prove this hypothesis is equivalent to global existence of smooth solutions for every smooth periodic initial field.
```

```lean
def formal_claim : Prop :=
  ∀ ν : ℝ, PeriodicBKMIntegrability ν → Clay_B_exact ν

/-- Paper (Section "Conditional results"): `(u, p)` is a smooth periodic solution on `[0, T]` with
data `u₀`: `T > 0`; `u(t)`, `p(t)` are `ℤ³`-periodic (unit shifts) for `t ∈ [0, T]`; `u`, `p` are
`C^∞` on `[0, T] × ℝ³`; `∂ₜu + (u·∇)u = νΔu - ∇p` and `div u = 0` on `[0, T] × ℝ³`, with `∂ₜ` the
derivative within `[0, T]`; `u(0) = u₀`. -/
def paperSolOn (ν : ℝ) (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (T : ℝ)
    (u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (p : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ) : Prop :=
  0 < T ∧
  (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x (j : Fin 3), u t (x + EuclideanSpace.single j 1) = u t x) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x (j : Fin 3), p t (x + EuclideanSpace.single j 1) = p t x) ∧
  ContDiffOn ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => u q.1 q.2)
    (Set.Icc (0 : ℝ) T ×ˢ Set.univ) ∧
  ContDiffOn ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => p q.1 q.2)
    (Set.Icc (0 : ℝ) T ×ˢ Set.univ) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
    derivWithin (fun s => u s x) (Set.Icc (0 : ℝ) T) t + fderiv ℝ (u t) x (u t x) =
      ν • ∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ (u t) y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1) - ∇ (p t) x) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
    ∑ i : Fin 3, fderiv ℝ (fun y => u t y i) x (EuclideanSpace.single i 1) = 0) ∧
  (∀ x, u 0 x = u₀ x)

/-- Paper: `T*(u₀) ∈ [-∞, ∞]`, the supremum of the real `T` for which a smooth periodic solution on
`[0, T]` with data `u₀` exists. -/
noncomputable def paperTstar (ν : ℝ)
    (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) : EReal :=
  sSup {s : EReal | ∃ T : ℝ, s = (T : EReal) ∧ ∃ u p, paperSolOn ν u₀ T u p}

/-- Paper: `∇ × v = (∂₂v₃ - ∂₃v₂, ∂₃v₁ - ∂₁v₃, ∂₁v₂ - ∂₂v₁)` (indices `0, 1, 2` here). -/
noncomputable def paperCurl (v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single 0 (fderiv ℝ (fun y => v y 2) x (EuclideanSpace.single 1 1) -
      fderiv ℝ (fun y => v y 1) x (EuclideanSpace.single 2 1)) +
    EuclideanSpace.single 1 (fderiv ℝ (fun y => v y 0) x (EuclideanSpace.single 2 1) -
      fderiv ℝ (fun y => v y 2) x (EuclideanSpace.single 0 1)) +
    EuclideanSpace.single 2 (fderiv ℝ (fun y => v y 1) x (EuclideanSpace.single 0 1) -
      fderiv ℝ (fun y => v y 0) x (EuclideanSpace.single 1 1))

/-- Paper: the hypothesis of Section "Conditional results". For `ν > 0`, every smooth,
divergence-free, `ℤ³`-periodic `u₀` and every `(u, p)` that is a smooth periodic solution on `[0, T]`
with data `u₀` for every real `T` with `0 < T < T*(u₀)`, the function
`t ↦ ‖ω(t)‖_∞ = sup_x |(∇ × u(t))(x)|` is integrable on `[0, T]` for every real `T`. -/
def paperBKMInt (ν : ℝ) : Prop :=
  0 < ν → ∀ u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
    ContDiff ℝ (⊤ : ℕ∞) u₀ →
    (∀ x, ∑ i : Fin 3, fderiv ℝ (fun y => u₀ y i) x (EuclideanSpace.single i 1) = 0) →
    (∀ x (j : Fin 3), u₀ (x + EuclideanSpace.single j 1) = u₀ x) →
    ∀ (u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (p : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ),
      (∀ T : ℝ, 0 < T → (T : EReal) < paperTstar ν u₀ → paperSolOn ν u₀ T u p) →
      ∀ T : ℝ, MeasureTheory.IntegrableOn (fun t => ⨆ x, ‖paperCurl (u t) x‖) (Set.Icc 0 T)

/-- Paper: Statement (B) holds conditionally on the hypothesis, spelled out. -/
def paper_claim : Prop :=
  ∀ ν : ℝ, 0 < ν → paperBKMInt ν →
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
```

See the doc comment of `PeriodicNSContinuation/Semantics.lean` for the fixed reading of the paper's terms and the scope.

## Re-certification (2026-11-23): new lock, certifying

Status: **certifying**, by the author's sign-off. This section supersedes the status line of the
re-audit below, which is kept as history.

Author's sign-off (Benjamin Stanley Frohman, 23 November 2026, 15:56 CST, America/Chicago, chosen on
an approval card), verbatim:
* "Yes, finish the new-lock transcription PR and correct the paper's sentence to integrable on [0,T] for every real T."
* "Yes, I sign off on certifying: true."

What changed:
* The paper's hypothesis sentence (Section "Conditional results") was corrected to say what
  `PeriodicBKMIntegrability` states: integrability of `t ↦ ‖ω(t)‖_∞` on `[0, T]` for **every real
  `T`** along every maximal solution, not only "on every finite interval of existence".
* `paper_claim` no longer names `PeriodicBKMIntegrability`. It uses `paperBKMInt`, written from the
  corrected sentence with Mathlib only (`paperSolOn`, `paperTstar`, `paperCurl`,
  `MeasureTheory.IntegrableOn`). `bkmInt_iff : PeriodicBKMIntegrability ν ↔ paperBKMInt ν` is proved
  by unfolding both sides and transporting across `solOn_iff`, `tstar_eq`, `supNorm_eq` and
  `data_iff` (no `rfl` correspondence; it does not use the main theorem).
* `formal_claim`, the main theorem and the gate scripts are unchanged.

Caveats the author acknowledged:
* **Partial lock.** The lock covers Statement (B) conditional on the transcribed hypothesis
  (`clay_B_exact_of_integrability`). The paper's other results are not locked. The quoted sentence
  on equivalence with global existence is context; that equivalence is not part of `formal_claim`.
* **Non-vacuity is not certified.** The hypothesis is open and is equivalent to global existence
  (`periodicBKMIntegrability_iff_globalLifespan`); no witness exists here. Nothing here proves
  Statement (B), global regularity, or the Clay Millennium problem.

## Re-audit (2026-11-16): this lock is NOT certifying

Status: **REOPENED. The gate is red on purpose.** `TRUTH_GATE.lock` carries `"certifying": false`, and
`scripts/truth_gate_check.py` fails while it does. Nothing was deleted: `Semantics.lean`, the quotes,
the hashes and the history are unchanged.

Rule applied (Benjamin Stanley Frohman, 2026-11-16):
* There are no partial locks. A lock certifies only a step on the correct path to the full theorem
  that is kernel-proved as the actual true answer, so that the next step can build on it.
* Drifted, dummy, placeholder or stand-in types, names or categories are rejected.
* Cross-ontology connections are not rejected for looking unrelated. The kernel check, and whether
  the piece genuinely helps reach the full structured proof, decide.
* `paper_claim` is an independent transcription of the verbatim paper quote, never an alias of
  `formal_claim`, and the correspondence is never `rfl`/`Iff.rfl`.

Locked claim under review: clay_B_exact_of_integrability (Statement (B) conditional on PeriodicBKMIntegrability)

Why it is reopened:
* The hypothesis is not independently transcribed. `paper_claim` keeps the repository Prop `PeriodicBKMIntegrability` as a named Prop. The paper describes it only loosely ("∫‖ω‖_∞ < ∞ on every finite interval of existence"), so the hypothesis that carries the whole difficulty is read through a repository definition.
* Non-vacuity is not certified. The hypothesis is open, there is no witness, and the paper says it is equivalent to global existence.

What would re-certify it: Re-lock with the hypothesis transcribed from a precise statement in the paper. BenFrohman/Clay- locks the same reduction with both hypotheses transcribed from the paper's English.
