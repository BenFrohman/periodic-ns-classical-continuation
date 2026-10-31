# periodic-ns-classical-continuation

Lean 4 + Mathlib formalization of the classical continuation steps used by the Statement (B)
route in `fefferman-clay-navier-stokes` (pinned at commit `ebcf109`, which has the corrected
definitions). It does **not** solve the Clay Navier–Stokes problem; the open step
`PeriodicBKMIntegrability` remains a hypothesis.

Build: `lake build`. Axiom check: `lake env lean AxiomAudit.lean` (only `propext`,
`Classical.choice`, `Quot.sound`; no `sorry`).

Dependencies: Mathlib, `fefferman-clay-navier-stokes` @ `ebcf109`,
`weighted-enstrophy-identities` @ `1df4652` (for `torusIntegral` and its derivative).

## Fully proved

* `periodicEnergyDifferenceEstimate (hν : 0 ≤ ν) : PeriodicEnergyDifferenceEstimate ν`
  (`Energy.lean`). For two classical periodic solutions with the same data, with `w = u − v`,
  `E(t) = ∫_{[0,1]³} |w|²` satisfies `E' ≤ 2C E`, where `C` bounds `‖∇v‖` on `[0,T] × [0,1]³`.
  Supporting files: `TorusIntegral.lean` (positivity), `TorusField.lean` (periodic divergence
  theorem on the unit cell), `FieldIdentities.lean` (divergence-form identities for the
  convective, viscous and pressure terms), `Clamp.lean` (time extension used to differentiate E).
* Pressure is unique up to a function of time: `normP_eq_of_velocity_eq`.
* Grönwall step: `eq_zero_of_deriv_le_mul`, `periodicVelocityUniqueness_of_energy`.
* Maximal solution by gluing: `periodicMaximalSolution_of_uniqueness`.
* `periodicGlobalOfTstarTop` (no hypotheses).
* Reductions `clay_B_exact_of_corrected_route` and `clay_B_exact_of_corrected_route'`
  (the second has no energy hypothesis).

## Still hypotheses (named Props)

* `PeriodicLocalExistence` — classical local existence (Kato). Not formalized.
* `PeriodicBKMCriterion` — classical Beale–Kato–Majda. Not formalized.
* `PeriodicBKMIntegrability` — open.

## Torus Sobolev foundation (`PeriodicNSContinuation/TorusSobolev.lean`)

`Hˢ(𝕋³)` for scalar `ℂ`-valued `L²` functions on `UnitAddTorus (Fin 3)`, defined by Fourier
weights `(1 + |k|²)ˢ`. Everything below is **proved**, with no hypotheses:

* `sobolevWeight_pos`, `sobolevWeight_mono` (monotone in `s`), `sobolevWeight_neg`.
* Norm facts: `sobolevNormSqSeq_nonneg`, `sobolevNormSqSeq_eq_zero_iff`, `sobolevNormSqSeq_smul`,
  closure under `+` and scalars (`MemSobolevSeq.add`, `MemSobolevSeq.smul`).
* `Hᵗ ⊆ Hˢ` for `s ≤ t` (`MemSobolevSeq.mono`, `sobolevNormSqSeq_mono`).
* `H⁰ = L²` by Mathlib's Parseval: `memSobolev_zero`, `sobolevNormSq_zero`
  (`‖f‖²_{H⁰} = ∫ ‖f‖²`), and `integral_sq_le_sobolevNormSq` for `s ≥ 0`.
* `summable_sobolevWeight_neg`: `∑_{k∈ℤ³} (1+|k|²)^{-s} < ∞` for `s > 3/2`.
* **Sobolev embedding** `sobolev_embedding_continuous`: for `s > 3/2`, every `f ∈ L² ∩ Hˢ` equals
  a.e. a continuous function, and its Fourier series converges to it uniformly.

Not yet done: vector-valued fields, the triangle inequality for the `Hˢ` norm, algebra/product
estimates and commutator estimates. These are still needed before `PeriodicLocalExistence`
can be discharged, so that hypothesis remains open.

## LocalExistence (concrete Galerkin link)

This package now depends on `torus-fourier-ns-lemmas` @ `ed0da95` (same Mathlib rev). The
uniform bound is no longer an arbitrary predicate. `GalerkinUniformBoundNS ν s u₀ T` says that,
for every `N`, a solution of the concrete truncated Leray-projected system
`TorusFourierNS.galerkinNSField N ν` exists on `[0,T]`, starts from the truncation of
`fourierCoeffVF u₀`, and has `H^s` norm `≤ M`, with `M` independent of `N`.

**Proved:**
- `periodicTstar_pos_of_solution`.
- `periodicLocalExistence_of_galerkin`: `PeriodicGalerkinUniformTime ν s` together with
  `PeriodicGalerkinLimit ν s` gives `PeriodicLocalExistence ν`.
- `periodicGalerkinUniformTime_of`: `PeriodicGalerkinUniformTime ν s` follows from
  `PeriodicDataHs s`, `TorusFourierNS.GalerkinTransportBound s C`,
  `GalerkinStructurePreserved ν` and `GalerkinContinuation ν s` (for `ν ≥ 0`, `C ≥ 0`). The time is
  explicit: `barrierTime C ‖û₀‖²_{H^s}`.
- `fourierCoeffVF_hermitian`: the Fourier coefficients of a real field are Hermitian.
- `galerkinStructurePreserved_of`: `GalerkinStructurePreserved ν` follows from `PeriodicDataDivFree`
  (it uses the proved preservation theorems `TorusFourierNS.galerkinNS_structure_Icc`).
- `periodicGalerkinUniformTime_of_gt`: for `ν ≥ 0` and **`s > 5/2`**, `PeriodicGalerkinUniformTime ν s`
  follows from `PeriodicDataHs s`, `PeriodicDataDivFree` and `GalerkinContinuation ν s` only. The
  transport bound is now proved (`TorusFourierNS.galerkinTransportBound_of_gt`, `s > 5/2`).

**Now proved (`PeriodicNSContinuation/FourierData.lean`):** `periodicDataHs s` (every real `s`),
`periodicDataDivFree`, `galerkinContinuation ν s`, hence
`periodicGalerkinUniformTime_of_gt' (hν : 0 ≤ ν) (hs : 5/2 < s) : PeriodicGalerkinUniformTime ν s`
with no named-Prop inputs. Method: integration by parts on the unit cell `[0,1]³`
(`cubeCoeff (∂_j g) k = 2πi k_j · cubeCoeff g k` for smooth `1`-periodic `g`), iterated
`(1 - Δ/4π²)`, the trivial bound `|ĝ(k)| ≤ sup |g|`, and the Galerkin continuation theorem
from `TorusFourierNS` (pin bumped to `878ce97`).

**NOT proved (explicit named-Prop input):** `PeriodicGalerkinLimit` (compactness, passage to the
limit, smoothness, pressure). `GalerkinTransportBound` for `3/2 < s ≤ 5/2` is not covered. So
`PeriodicLocalExistence` (Kato) is still conditional, and Clay is not solved.

Coined names in `FourierData`: `cubeCoeff`, `pdC`, `insertNth_one_eq`, `integral_pdC_eq_zero`,
`charK`, `cubeCoeff_eq`, `phaseCLM`, `phaseCLM_apply`, `charK_eq`, `charK_contDiff`,
`charK_hasFDerivAt`, `phaseCLM_single`, `charK_add_single`, `norm_charK`, `cubeCoeff_pdC`,
`compC`, `fourierCoeffVF_eq_cubeCoeff`, `equiv_symm_single`, `compC_contDiff`,
`compC_add_single`, `pdC_compC`, `periodicDataDivFree`, `SmoothPer`, `SmoothPer.pdC`,
`SmoothPer.continuous`, `helmOp`, `SmoothPer.helmOp`, `integrableOn_coeff`, `cubeCoeff_helmOp`,
`smoothPer_iterate_helmOp`, `cubeCoeff_iterate_helmOp`, `exists_bound_cubeCoeff`,
`summable_sobW_cubeCoeff`, `periodicDataHs`, `galerkinContinuation`,
`periodicGalerkinUniformTime_of_gt'`.

Coined names: `fourierCoeffVF`, `IsGalerkinSolutionOn`, `GalerkinUniformBoundNS`,
`PeriodicGalerkinUniformTime`, `PeriodicGalerkinLimit`, `PeriodicDataHs`,
`GalerkinStructurePreserved`, `GalerkinContinuation`, `PeriodicDataDivFree`,
`fourierCoeffVF_hermitian`, `galerkinStructurePreserved_of`, `periodicGalerkinUniformTime_of_gt`.

## GalerkinLimit (`GalerkinLimit.lean`, `GalerkinLimitProof.lean`)

`PeriodicGalerkinLimit ν s` is split into named sub-Props (all coined). The first two are now
**proved for `s > 2`**; the third is **NOT proved**:

* `GalerkinModeEquiLipschitz ν s`: each Fourier mode of the Galerkin solutions is Lipschitz in
  time, uniformly in `N`. This should follow from the ODE and the uniform `H^s` bound via a
  Cauchy–Schwarz bound on the truncated convolution and the mean value theorem.
* `GalerkinLimitEquation ν s`: the mode-wise limit satisfies the integrated full Fourier NS
  equation `a t = a 0 + ∫₀ᵗ fourierNSField ν (a τ)`.
* `FourierSolutionReconstruction ν s`: an `H^s`, Hermitian, divergence-free Fourier solution
  from smooth data yields smooth periodic `u`, `p` (`IsPeriodicSmoothSolutionOn`). This needs
  propagation of higher regularity and is not covered by a single `H^s` bound.

**Proved:**
* `exists_subseq_tendsto_of_equiLipschitz`: a diagonal Arzelà–Ascoli argument over rational times
  and countably many coordinates.
* `galerkinModeConvergence_of`: equi-Lipschitz implies `GalerkinModeConvergence`.
* Properties the limit inherits: `limit_initial`, `hermitian_of_tendsto`,
  `divergenceFree_of_tendsto`, and `hs_of_tendsto` (Fatou: `MemHsField s` and `hsNormField ≤ M`).
* `norm_extendG_le_of_hs`, `summable_hs_extendG`, `eventually_mem_modeBox`.
* `periodicGalerkinLimit_of` (from `GalerkinModeConvergence`, `GalerkinLimitEquation` and
  `FourierSolutionReconstruction`) and `periodicGalerkinLimit_of'` (from the equi-Lipschitz
  Prop instead).

**Proved for `s > 2` (`GalerkinLimitProof.lean`):**
* `galerkinModeEquiLipschitz (hs : 2 < s) : GalerkinModeEquiLipschitz ν s`.
* `galerkinLimitEquation (hs : 2 < s) : GalerkinLimitEquation ν s`.
* `periodicGalerkinLimit_of_reconstruction (hs : 2 < s) : FourierSolutionReconstruction ν s →
  PeriodicGalerkinLimit ν s`.
* Key estimate `norm_convTerm_le`: under the pointwise decay `‖a m l‖ ≤ M (1+|m|²)^{-s/2}`
  (implied by `hsNormField s ≤ M`), the convolution term is `≤ convConst s M k · (1+|m|²)^{-(s-1/2)}`
  (Peetre's inequality `bse_le`). That is summable in `m` exactly when `s > 2`, which is why the
  hypothesis appears. The Props as stated for all `s` are not claimed. The use case `s > 5/2` is covered.
* Supporting lemmas: `norm_lerayP_le`, `norm_fourierNSField_le` (uniform mode bound `lipC`),
  `galerkinNSField_eq` (inside the box the Galerkin field equals `fourierNSField` of `extendG u`),
  `galerkin_component`, and `tendsto_fourierNSField` (Tannery's theorem). The limit equation uses the
  FTC for each `N` and dominated convergence.

So `PeriodicGalerkinLimit`, and hence `PeriodicLocalExistence`, is still conditional, now only on `FourierSolutionReconstruction` (for `s > 2`). Clay is not solved.

Coined names: `fourierNSField`, `GalerkinModeConvergence`, `GalerkinLimitEquation`,
`FourierSolutionReconstruction`, `GalerkinModeEquiLipschitz`, `convTerm`, `PtBound`, `bse`,
`convConst`, `bseSum`, `lipC`, and every theorem listed above.

## Reconstruction (`PeriodicNSContinuation/Reconstruction.lean`)

`FourierSolutionReconstruction ν s` is split into three named sub-Props (all coined, **NOT proved**):

* `FourierHigherRegularity ν s`: an `H^s` Fourier solution (`IsFourierSolutionOn`) from smooth
  data is bounded in `H^{s'}` on `[0,T]` for every `s'`.
* `FourierSeriesVelocity ν`: for a solution bounded in every `H^{s'}` (`IsSmoothFourierSolutionOn`),
  the inverse Fourier series `seriesVelocity a` is jointly `C^∞` on `[0,T] × ℝ³`, divergence-free,
  and equals `u₀` at `t = 0`. That last part needs Fourier inversion for smooth periodic `u₀`.
* `PeriodicPressureRecovery ν`: `seriesPressure a`, with coefficients
  `p̂ = pressureCoeff k N̂ = -(k·N̂)/(2πi|k|²)`, is jointly `C^∞`, and the pair satisfies the
  momentum equation.

**Proved:**
* `fourierSolutionReconstruction_of`: the three Props imply `FourierSolutionReconstruction`.
* `periodicGalerkinLimit_of_subProps (hs : 2 < s)`: the three Props imply `PeriodicGalerkinLimit`.
* `seriesVelocity_periodic`, `seriesPressure_periodic` (via `phase_periodic` and `seriesC_periodic`):
  `ℤ³`-periodicity holds for any coefficients, so it is not an assumption.
* `conj_phase` and `conj_seriesC_of_hermitian`: Hermitian coefficients give a real series.
* `neg_lerayP_eq` and `fourierNSField_eq_pressure`:
  `fourierNSField ν a k i = -visc·a k i - N̂ k i - 2πi kᵢ p̂ k`. This is the Fourier-side form of
  `∂ₜu + (u·∇)u = νΔu - ∇p`, i.e. pressure recovery at the coefficient level.

So `PeriodicLocalExistence` is still conditional, now on these three Props (for `s > 2`).
Clay is not solved.

Coined names: `phase`, `seriesC`, `seriesVelocity`, `nonlinCoeff`, `pressureCoeff`, `seriesPressure`,
`IsFourierSolutionOn`, `IsSmoothFourierSolutionOn`, `FourierHigherRegularity`,
`FourierSeriesVelocity`, `PeriodicPressureRecovery`, and every theorem listed above.

## Fourier inversion (`PeriodicNSContinuation/FourierInversion.lean`)

**Proved:**
* `fourierCoeffVF_hasSum`: 3D Fourier inversion for smooth periodic data. If `u₀` is smooth and
  periodic, then for every `x` the series `Σ_k fourierCoeffVF u₀ k i · e^{2πi k·x}` converges
  (absolutely) to `u₀ x i`.
  The proof descends each component to `C(UnitAddTorus (Fin 3), ℂ)` (`torusCompC`) and identifies
  Mathlib's `mFourierCoeff` with `fourierCoeffVF` (`mFourierCoeff_torusCompC`). Absolute
  summability (`summable_norm_fourierCoeffVF`) comes from `periodicDataHs 2`. It then applies
  Mathlib's `hasSum_mFourier_series_apply_of_summable`.
* `seriesVelocity_zero`: if `a 0 = fourierCoeffVF u₀`, then `seriesVelocity a 0 = u₀`.
* `fourierSeriesVelocity_of`: `FourierSeriesVelocitySmooth ν → FourierSeriesVelocity ν`.
* `periodicGalerkinLimit_of_subProps' (hs : 2 < s)`: `FourierHigherRegularity`,
  `FourierSeriesVelocitySmooth` and `PeriodicPressureRecovery` imply `PeriodicGalerkinLimit`.

**NOT proved:**
* `FourierSeriesVelocitySmooth ν`: joint `C^∞` on `[0,T] × ℝ³` and zero divergence.
* `PeriodicPressureRecovery ν`.
* `FourierHigherRegularity ν s` (the tame `H^{s'}` estimate).

`PeriodicLocalExistence` is still conditional. Clay is not solved.

Coined names: `compR`, `torusMk`, `torusComp`, `torusCompC`, `mFourier_torusMk`, `norm_le_aux`,
`FourierSeriesVelocitySmooth`, and every theorem listed above.

## Higher regularity (`PeriodicNSContinuation/HigherRegularity.lean`)

This uses the tame Galerkin estimate now proved in torus-fourier-ns-lemmas (`TameTransport.lean`;
the dependency pin is bumped to `2356dcb`).

**Proved:**
* `hs_bound_of_galerkin (0 ≤ ν) (5/2 < s)`: a mode-wise limit of Galerkin solutions from smooth
  data, with the solutions Hermitian, divergence-free and uniformly bounded in `H^s`, is bounded in
  every `H^{s'}`. The proof applies Grönwall with the tame bound `‖·‖_{H^{s₀}}·‖·‖²_{H^r}` at
  `r = max s' 2`, then truncation monotonicity, then Fatou (`hs_of_tendsto`).
* `hsNormField_extendG_mono`: Galerkin `H^s` norms are monotone in `s`.
* `periodicGalerkinLimit_of_velocity_pressure (0 ≤ ν) (5/2 < s)`:
  `FourierSeriesVelocitySmooth ν → PeriodicPressureRecovery ν → PeriodicGalerkinLimit ν s`.
  Reconstruction is applied to the Galerkin subsequence limit that the proof builds, so its
  approximation data is available. No uniqueness statement is needed.

The earlier Prop `FourierGalerkinApproximation` (and `fourierHigherRegularity_of`,
`periodicGalerkinLimit_of_subProps''`) has been removed: it is no longer needed.

**NOT proved:** `FourierSeriesVelocitySmooth ν` and `PeriodicPressureRecovery ν`.

Note: this route needs `s > 5/2` (the tame bound's `ℓ¹` factor), stronger than the `s > 2` used
earlier. `PeriodicGalerkinLimit`, and therefore `PeriodicLocalExistence`, is still conditional on
those two Props. Clay is not solved.

Coined names: `hsNormField_extendG_mono`, `hs_bound_of_galerkin`,
`periodicGalerkinLimit_of_velocity_pressure`.
