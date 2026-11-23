# Kernel certificate: periodic-ns-classical-continuation

This file records a reproducible machine check of the Lean 4 development in this repository. Lean does not issue a signed "official" certificate. What is recorded here is the exact commit and toolchain, the complete `lake build` log, a scan for `sorry`/`admit`/`native_decide`/`axiom`, the `#print axioms` result for every theorem the build produces, and a replay of every module through Lean's kernel with the toolchain's `leanchecker`. Each check can be rerun with the command at the end.

| Item | Value |
|---|---|
| Repository | https://github.com/BenFrohman/periodic-ns-classical-continuation |
| Certified commit | `b5154f38e928c76f599812ba76074fb37e4ead3a` (`main`, merge of PR #6) |
| Lean sources | relative to the previous certificate (`4aa277f`), the only `.lean` changes are the new files `PeriodicNSContinuation/Semantics.lean` and `scripts/TruthGateAudit.lean`; neither is imported by the root module, so neither is among the 78 built modules below (both are checked by the `truth-gate` workflow, see [TRUTH_GATE.md](../TRUTH_GATE.md)) |
| lean-toolchain | `leanprover/lean4:v4.30.0-rc1` |
| Lean | Lean (version 4.30.0-rc1, x86_64-unknown-linux-gnu, commit 714601baf118066cbf3f282361339c6d06665b2a, Release) |
| Mathlib | `0c154d67103f74be3a0f2c509f72ccbf5be9f2a7` (lake-manifest.json; inputRev `v4.30.0-rc1`) |
| Lake | Lake version 5.0.0-src+714601b (Lean version 4.30.0-rc1) |
| Date | 2026-11-17T10:10:37Z (UTC) = 17 November 2026, 04:10 CST (America/Chicago) |
| CI run | https://github.com/BenFrohman/periodic-ns-classical-continuation/actions/runs/44062315856 (workflow `Kernel certificate`, push to `main`, conclusion `success`) |
| `lake build` | `Build completed successfully (8369 jobs).` ([build.log](build.log)) |
| sorry / admit / native_decide / axiom scan | `RESULT: 0 hits` over 82 tracked `.lean` files ([sorry-scan.txt](sorry-scan.txt)); 0 `declaration uses 'sorry'` warnings in [build.log](build.log) |
| `#print axioms` | `AUDIT PASS: 1052 theorems in 77 modules depend only on propext, Classical.choice, Quot.sound (or on no axioms)` ([axioms.txt](axioms.txt)) |
| Kernel replay (leanchecker) | `RESULT: 78 of 78 modules replayed through the kernel, 0 failures` ([leanchecker.txt](leanchecker.txt)) |

## What each check means

- **Build.** `lake build` of the default targets with the pinned toolchain. Mathlib comes from `lake exe cache get` (it is never rebuilt from source). The build elaborates every proof and sends each declaration to Lean's kernel.
- **Scan.** `certificates/tools/sorry_scan.py` strips comments and strings from every tracked `.lean` file and reports any `sorry`, `admit`, `native_decide` or `axiom` declaration. Result: RESULT: 0 hits.
- **Axioms.** `certificates/tools/gen_audit.py` imports all 78 built modules ([modules.txt](modules.txt)) and calls `Lean.collectAxioms`, the function behind `#print axioms`, on every theorem declared in them (1052 theorems, auto-generated internal names excluded). `check_audit.py` fails unless each depends only on `propext`, `Classical.choice` and `Quot.sound`, or on no axioms. Raw output: [axioms.raw.txt](axioms.raw.txt); generated Lean file: [KernelCertificateAudit.lean.txt](KernelCertificateAudit.lean.txt).
- **Kernel replay.** checker: leanchecker source shipped with v4.30.0-rc1 (src/lean/LeanChecker.lean), prefix match -> exact match, run with lean --run. For each module, the checker loads the module's imports from their `.olean` files and replays every declaration of that module through the kernel. The stock checker treats its argument as a module-name prefix and replays all matching modules in parallel, which runs out of memory on a root module, so it is run once per module with exact matching (the one-line patch is printed in [leanchecker.txt](leanchecker.txt)). The checker's own documentation describes it as a tool to detect environment hacking, not an independent external verifier; imported Mathlib and core declarations are trusted from their `.olean` files.

## Scope

The repository's `truth-gate` check (the paper ↔ Lean lock, [TRUTH_GATE.md](../TRUTH_GATE.md)) is **red** on this commit: `VERDICT: FAIL (LOCK-FORM). Kernel checks passed: no math was found false.` ([run 44062315706](https://github.com/BenFrohman/periodic-ns-classical-continuation/actions/runs/44062315706)). The lock is marked not certifying because `paper_claim` still reads the hypothesis `PeriodicBKMIntegrability` through the repository's own definition. This file is therefore a kernel certificate for the Lean development only; it does not certify that the paper's English claim is the statement Lean proves.

The axiom result says the listed theorems are proved from Lean's standard axioms. It does not by itself say what the theorems mean; read the statements in the sources. Conditional theorems remain conditional on their hypotheses.

## Rebuild

```
git clone https://github.com/BenFrohman/periodic-ns-classical-continuation.git && cd periodic-ns-classical-continuation && git checkout b5154f38e928c76f599812ba76074fb37e4ead3a && lake exe cache get && lake build && python3 certificates/tools/sorry_scan.py && python3 certificates/tools/gen_audit.py /tmp/KernelCertificateAudit.lean /tmp/modules.txt && lake env lean /tmp/KernelCertificateAudit.lean > /tmp/axioms.raw.txt && python3 certificates/tools/check_audit.py /tmp/axioms.raw.txt | tail -n 1
```
