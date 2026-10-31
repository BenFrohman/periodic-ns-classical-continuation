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

* `PeriodicLocalExistence` — **now proved** for `ν ≥ 0` (`periodicLocalExistence_of_nonneg`, see below); no longer a hypothesis.
* `PeriodicBKMCriterion` — classical Beale–Kato–Majda. Now reduced to `PeriodicBKMHsControl` (see below); the blow-up alternative is proved.
* `PeriodicBKMIntegrability` — open.
* `PeriodicPhysicalCommutatorBound C` (s = 3, coined) — proved sufficient for `PeriodicFourierCommutatorBound 3 C`, and now **proved** (`periodicPhysicalCommutatorBound`, CommutatorAssembly.lean), with C = 2·64·315·64·(4π²)³.

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

## Reconstruction of the smooth solution (`CoefSpace`, `TimeCurve`, `SpatialSeries`, `SeriesCalculus`, `PDE`, `SmoothReconstruction`)

**Proved, no hypothesis Props:** `periodicGalerkinLimit_of_nonneg (0 ≤ ν) (5/2 < s) :
PeriodicGalerkinLimit ν s`. The Galerkin limit inherits the equi-Lipschitz bound
(`galerkinModeEquiLipschitz`), so each mode is continuous in time (`modeContinuous_of_tendsto`).
Then the reconstruction below applies.

**Proved, given mode continuity (`ModeContinuous T a`):**
* `fourierSeriesVelocitySmooth_of_modeCont`: the conclusion of `FourierSeriesVelocitySmooth`
  (joint `C^∞` on `[0,T] × T3`, zero divergence).
* `periodicPressureRecovery_of_modeCont`: the conclusion of `PeriodicPressureRecovery` (joint
  `C^∞` pressure and the momentum equation).

Method: the weighted coefficients form a `C^∞` curve in an `ℓ¹` space (`CurveHyp.contDiffOn_infty`),
evaluated by a `C^N` linear evaluation map (`contDiff_evOp`). The derivatives of the series are
taken term by term, and the convective term is computed with a Cauchy product on `ℤ³`
(`seriesC_mul`, `seriesC_convective`).

**NOT proved:** `FourierSeriesVelocitySmooth ν` and `PeriodicPressureRecovery ν` *as stated*. Their
hypothesis `IsSmoothFourierSolutionOn` does not include mode continuity. The integral equation alone
does not force it, because a non-integrable integrand gives an interval integral of `0`. The theorem
`periodicGalerkinLimit_of_nonneg` avoids this gap.

## Local existence, proved (`PeriodicNSContinuation/LocalExistenceProof.lean`)

**Proved, with no hypothesis Props:** `periodicLocalExistence_of_nonneg (hν : 0 ≤ ν) : PeriodicLocalExistence ν`.
It combines `periodicGalerkinUniformTime_of_gt'` and `periodicGalerkinLimit_of_nonneg` at `s = 3`.
`PeriodicLocalExistence` does not quantify over `s`. Its solution notion is
`IsPeriodicSmoothSolutionOn` through `periodicTstar`, which is the notion used by `clay_B_exact_of_corrected_route'`.

**Conditional reduction:** `clay_B_exact_of_bkm (ν) (hcrit : PeriodicBKMCriterion ν)
(hint : PeriodicBKMIntegrability ν) : Clay_B_exact ν`. The only remaining hypotheses are
`PeriodicBKMCriterion` (classical BKM, not formalized here) and `PeriodicBKMIntegrability`.
`PeriodicBKMIntegrability` is **open**: it is the Millennium content. **Clay is not solved.**

Coined names: `periodicLocalExistence_of_nonneg`, `clay_B_exact_of_bkm`.

Coined names (all new): `CoefL1`, `mkL1`, `mulOp`, `wt`, `unw`, `cterm`, `bilRaw`, `bilOp`,
`viscMul`, `viscOp`, `lerayLin`, `lerayOp`, `pressLin`, `pressOp`, `emb`, `nsOp`, `evk`,
`CurveHyp`, `coefCurve`, `coefField`, `lin`, `linS`, `coordB`, `evTerm`, `evOp`, `HS`,
`AllHsBound`, `reVec`, `vecS`, `ModeContinuous`. Every lemma and theorem in these six files also
has a coined name.

Coined names: `hsNormField_extendG_mono`, `hs_bound_of_galerkin`,
`periodicGalerkinLimit_of_velocity_pressure`.

## BKM criterion split (`PeriodicNSContinuation/Continuation.lean`)

**Proved, no hypothesis Props** (`0 ≤ ν`, `5/2 < s`):
- `periodicLocalSolution_quant`: local existence on `[0, barrierTime C Y]` whenever `‖û₀‖²_{H^s} ≤ Y`
  (time depends only on the `H^s` bound).
- `shift_sol` (time shift), `glue_sol` (gluing two overlapping solutions).
- `periodicHsBlowupAlternative : PeriodicHsBlowupAlternative ν s`: a maximal solution with finite
  `T*` cannot stay bounded in `H^s` on `[0, T*)`.

**Not proved (named Prop):** `PeriodicBKMHsControl ν s`: along a maximal solution with finite `T*`,
`∫₀^{T*} ‖ω‖_∞ < ∞` implies `sup_{[0,T*)} ‖u‖_{H^s} < ∞`. This is the classical BKM core
(tame `H^s` estimate + logarithmic Sobolev inequality), not formalized here.

**Conditional:** `periodicBKMCriterion_of_hsControl : PeriodicBKMHsControl ν s → PeriodicBKMCriterion ν`
and `clay_B_exact_of_hsControl : PeriodicBKMHsControl ν s → PeriodicBKMIntegrability ν → Clay_B_exact ν`.
`PeriodicBKMIntegrability` is **open**. **Clay is not solved.**

Coined names: `barrierTime_anti`, `barrierTime_pos`, `periodicLocalSolution_quant`, `shift_sol`,
`glueR`, `glue_contDiffOn`, `glue_deriv`, `glue_sol`, `PeriodicHsBlowupAlternative`,
`periodicHsBlowupAlternative`, `PeriodicBKMHsControl`, `periodicBKMCriterion_of_hsControl`,
`clay_B_exact_of_hsControl`.

## Splitting `PeriodicBKMHsControl` (`PeriodicNSContinuation/BKMGronwall.lean`)

**Proved, no hypothesis Props:** `gronwall_of_hasDerivAt` (differential Grönwall with a continuous coefficient).

**Hypotheses (named Props, NOT proved here; classical and true for suitable constants):**
- `PeriodicTameHsInequality ν s C`: along smooth solutions, `t ↦ ‖u‖²_{H^s}` is continuous and
  differentiable with `d/dt ‖u‖²_{H^s} ≤ C ‖∇u‖_∞ ‖u‖²_{H^s}` (Kato–Ponce commutator estimate).
- `PeriodicSupNormContinuity ν`: `t ↦ ‖∇u(t)‖_∞` and `t ↦ ‖ω(t)‖_∞` are continuous. **Now proved** (`periodicSupNormContinuity`, see below).
- `PeriodicLogSobolevBKM s K`: `‖∇v‖_∞ ≤ K (1 + ‖ω‖_∞ (1 + log (1 + ‖v‖²_{H^s})))` for smooth
  periodic divergence-free `v` (Brezis–Gallouet / BKM).

The constants `C`, `K` are explicit arguments. The Props are true for some `C(s)`, `K(s)` when
`s > 5/2`, but those constants are not computed here. The Props are not vacuous because smooth
solutions exist (`periodicLocalSolution_quant`).

**Proved from them:**
- `periodicGradHsControl`: from tame inequality + continuity, `∫₀^{T*} ‖∇u‖_∞ < ∞` bounds `‖u‖_{H^s}`.
- `periodicBKMHsControl_of_tame_log`: from all three, `PeriodicBKMHsControl ν s`.
- `clay_B_exact_of_tame_log`: from all three plus the **open** `PeriodicBKMIntegrability ν`.

**Clay is not solved.**

Coined names: `gradSupNorm`, `hsSq`, `PeriodicTameHsInequality`, `PeriodicSupNormContinuity`,
`PeriodicLogSobolevBKM`, `PeriodicGradHsControl`, `gronwall_of_hasDerivAt`, `periodicGradHsControl`,
`periodicBKMHsControl_of_tame_log`, `clay_B_exact_of_tame_log`, plus the helpers `sol_around`,
`hsNorm_le_of_hsSq_le`, `u_zero`, `integral_le_of_nonneg`, `gradSupNorm_nonneg`, `hsSq_nonneg`.

## BKM pieces (`PeriodicNSContinuation/BKMPieces.lean`)

**Proved, no hypothesis Props:**
- `supNorm_continuousOn`, `periodicSupNormContinuity ν`: sup norms of `∇u` and `ω` are continuous in time.
- `fourier_split_bound`: for `s > 3/2` and `∑ (1+|k|²)^s c_k² < ∞`,
  `∑|c_k| ≤ ∑_{|k|≤R}|c_k| + (∑_{|k|>R}(1+|k|²)^{-s})^{1/2} ‖c‖_{H^s}`.
- `tailWeight_tendsto_zero` (the tail weight tends to 0 as `R → ∞`) and `fourier_split_eps`
  (for each `ε > 0` there is an `R` that gives `ε‖c‖_{H^s}`).
  These are the first Fourier-side steps of Brezis–Gallouet. The explicit rate
  `tailWeight s R ≲ R^{3-2s}`, the low-frequency bound and the choice `R ~ ‖u‖_{H^s}^{1/(s-3/2)}` are
  **not** done. The 3D BKM inequality with `‖ω‖_∞` also needs a Calderón–Zygmund/Littlewood–Paley
  bound for the low-frequency part, which is not formalized.

**Hypotheses, with constants quantified existentially and depending only on `s`:**
`PeriodicTameHsBound s := ∃ C ≥ 0, ∀ ν, PeriodicTameHsInequality ν s C` and
`PeriodicLogSobolevBKMBound s := ∃ K ≥ 0, PeriodicLogSobolevBKM s K`. NOT proved.

**Proved from them:** `periodicGradHsControl_of_bound`, `periodicBKMHsControl_of_bounds`.
**Conditional:** `clay_B_exact_of_bounds` (also needs the **open** `PeriodicBKMIntegrability ν`).
**Clay is not solved.**

Coined names: `supNorm_continuousOn`, `curlOf`, `continuous_single'`, `continuous_curlOf`,
`directionalCoord_eq`, `curl_eq_curlOf`, `periodicSupNormContinuity`, `PeriodicTameHsBound`,
`PeriodicLogSobolevBKMBound`, `periodicGradHsControl_of_bound`, `periodicBKMHsControl_of_bounds`,
`clay_B_exact_of_bounds`, `modeSq`, `tailWeight`, `cs_tsum`, `fourier_split_bound`,
`tailWeight_tendsto_zero`, `fourier_split_eps`.

## Brezis–Gallouet log step and Kato–Ponce start (`PeriodicNSContinuation/BKMLog.lean`)

**Proved, no hypothesis Props:**
- `tailWeight_le_rpow`: for `3/2 < s' ≤ s` and `R > 0`,
  `tailWeight s R ≤ R^{-2(s-s')} ∑_k (1+|k|²)^{-s'}`. This gives the rate `R^{-2δ}` for every `δ < s - 3/2`.
  The sharp endpoint `R^{3-2s}` needs lattice-shell counting, which is **not** proved. It is not needed for the log.
- `fourier_split_log`: with `δ = s-s'`, `N = ‖c‖_{H^s}` and `R = (1+N)^{1/δ}`,
  `∑|c_k| ≤ ∑_{|k|≤R}|c_k| + (∑(1+|k|²)^{-s'})^{1/2}` and `log R = log(1+N)/δ`.
- `bkm_log_arith`: the remaining arithmetic. The bounds `g ≤ low + tail`, `low ≤ K(1+log R)ω`, `tail ≤ B` and the
  log choice of `R` give `g ≤ K'(1 + ω(1+log(1+N)))` with an explicit `K'`.
- `vpWeight` (tensor de la Vallée Poussin weight) and its lemmas `vpWeight_nonneg`, `vpWeight_le_one`, `vpWeight_eq_one`
  and `vpWeight_eq_zero`.
- Kato–Ponce, Fourier side (start): `sobW_add_le`, which says `(1+|a+b|²)^s ≤ 4^s((1+|a|²)^s+(1+|b|²)^s)` for `s ≥ 0`,
  and `conv_term_split`, the pointwise split of a weighted convolution term.

**New hypothesis (true, not formalized):** `PeriodicLowFreqVorticityBound`. It says there is a `K ≥ 0` such that for all
`R ≥ 2` and every smooth periodic divergence-free `v`, `sup_x ‖V_R ∇v(x)‖ ≤ K(1+log R)‖ω‖_∞`. Here `V_R` is the de la
Vallée Poussin low-pass operator. It holds classically: the tensor Fejér kernel is bounded in `L¹`, Biot–Savart makes
`∇v` a Calderón–Zygmund transform of `ω`, and `O(log R)` Littlewood–Paley blocks are each bounded in `L^∞` by `C‖ω‖_∞`.
It is not vacuous, because `R ≥ 2` and nonzero `v` are allowed. **It is not proved here.**

**Not done:**
- Assembling `PeriodicLogSobolevBKMBound s` from these pieces. That needs the pointwise Fourier inversion
  `∇v = V_R∇v + (high-frequency part)`, with the high part bounded by `∑_{|k|_∞>R} |k||v̂_k|`.
- The full `PeriodicTameHsBound`: the commutator estimate and the energy identity in Fourier variables.
- `PeriodicBKMIntegrability` remains the **open** hypothesis. **Clay is not solved.**

Coined names: `modeSq_nonneg`, `tailWeight_le_rpow`, `fourier_split_log`, `vpWeight` (and its lemmas), `gradCoeff`,
`lowGrad`, `lowGradSup`, `PeriodicLowFreqVorticityBound`, `bkm_log_arith`, `modeSq_add_le`, `sobW_add_le`,
`conv_term_split`.

## BKM assembly (BKMAssembly.lean)

**Proved (no sorry, standard axioms only):**
- `periodicLogSobolevBKMBound_of_lowFreq`: for `s > 5/2`, `PeriodicLogSobolevBKMBound s` follows from the single hypothesis `PeriodicLowFreqVorticityBound`. Ingredients proved here: the Fourier series of `∂_j v_i` (`hasSum_grad`), the entrywise split into low frequencies plus tail (`entry_le`), the operator-norm-by-entries bound (`opNorm_le_entries`), the tail bound `≤ √tailWeight(s−1,R)·‖v‖_{H^s}` (`grad_tail_le`), and the choice `R = 2(1+‖v‖_{H^s})^{1/δ}`.
- `periodicBKMHsControl_of_tame_lowFreq`: `PeriodicBKMHsControl` from the tame hypothesis plus `PeriodicLowFreqVorticityBound`.
- Kato–Ponce split: `periodicTameHsInequality_of_fourier` derives `PeriodicTameHsInequality ν s C` from `PeriodicFourierHsEnergyIdentity ν s` and `PeriodicFourierCommutatorBound s C`. The viscous term is dropped by its sign (`visc_term_nonpos`). `periodicBKMHsControl_of_fourier_lowFreq` chains these.

**Still hypotheses (true classically, not proved here):**
- `PeriodicLowFreqVorticityBound` (low-frequency ‖∇u‖ ≲ (1+log R)‖ω‖_∞).
- `PeriodicFourierHsEnergyIdentity`: the Fourier coefficients of a classical solution satisfy `û' = fourierNSField ν û`, and the H^s norm differentiates termwise. The repo only has the reverse (reconstruction) direction.
- `PeriodicFourierCommutatorBound`: the commutator bound with ‖∇v‖_∞. The existing TorusFourierNS machinery (`weight_commutator_le`, `galerkinTameTransportBound_of_gt`) proves the tame bound in the H^{s₀}/Wiener norm, not in ‖∇v‖_∞. Closing that gap needs physical-space paraproducts.
- `PeriodicBKMIntegrability` remains open. **The Clay problem is not solved by this repository.**

Coined names: `ev`, `phase_shift`, `summable_mode_mul_coeff`, `norm_gradCoeff`, `hasSum_grad`, `abs_le_of_modeSq_le`, `lowGrad_eq`, `entry_le`, `opNorm_le_entries`, `grad_tail_le`, `lowGrad_norm_le`, `periodicLogSobolevBKMBound_of_lowFreq`, `periodicBKMHsControl_of_tame_lowFreq`, `nlField`, `fourierNSField_eq`, `rateOf`, `PeriodicFourierHsEnergyIdentity`, `PeriodicFourierCommutatorBound`, `visc_term_nonpos`, `periodicTameHsInequality_of_fourier`, `periodicBKMHsControl_of_fourier_lowFreq`.

## Energy identity reduction (HsEnergyIdentity.lean)

**Proved (no sorry, standard axioms only):**
- `fourierCoeffVF_continuousOn`: every Fourier coefficient of a classical solution is continuous in time on `[0, T']` (from joint smoothness, as a parametric integral over the compact unit cell).
- `hasDerivAt_normSq_complex`: `d/dt ‖z(t)‖² = 2 Re(conj z · z')`.
- `periodicFourierHsEnergyIdentity_of_coeff`: for every real `s`, `PeriodicFourierHsEnergyIdentity ν s` follows from two narrower hypotheses, `PeriodicFourierCoeffODE ν` and `PeriodicFourierCoeffDecay ν`. The termwise differentiation (`hasDerivAt_tsum_of_isPreconnected`), the summability of the rate, and the continuity of `t ↦ ‖u(t)‖²_{H^s}` are proved.
- `periodicBKMHsControl_of_coeff_lowFreq`: BKM `H^s` control from `PeriodicFourierCoeffODE`, `PeriodicFourierCoeffDecay`, `PeriodicFourierCommutatorBound` and `PeriodicLowFreqVorticityBound`.

**New hypotheses (they replace `PeriodicFourierHsEnergyIdentity`; both are now proved in CoeffODE.lean):**
- `PeriodicFourierCoeffODE ν`: on `(0, T')`, each coefficient satisfies `û' = fourierNSField ν û`. This needs differentiation under the integral, integration by parts for the Laplacian and pressure, the convolution formula for `(u·∇)u`, and the Leray projection.
- `PeriodicFourierCoeffDecay ν`: for every `r` there is one `B` with `‖û(t)_k‖, ‖fourierNSField ν û(t)_k‖ ≤ B⟨k⟩^{-2r}` for all `t ∈ [0, T']`. This needs `(1−Δ)^m` bounds for the jointly smooth `u` and `∂ₜu`.
- `PeriodicBKMIntegrability` remains open. **The Clay problem is not solved by this repository.**

Coined names: `hasDerivAt_normSq_complex`, `PeriodicFourierCoeffODE`, `PeriodicFourierCoeffDecay`, `fourierCoeffVF_continuousOn`, `hsSq_eq_tsum`, `summable_prod_fin3`, `sobW_mul_sobW`, `rate_term_le`, `sq_term_le`, `periodicFourierHsEnergyIdentity_of_coeff`, `periodicBKMHsControl_of_coeff_lowFreq`.

## Coefficient ODE and decay (CoeffODE.lean)

**Proved (no sorry, standard axioms only):**
- `periodicFourierCoeffODE ν : PeriodicFourierCoeffODE ν`. On `(0, T')` the Fourier coefficients of a classical periodic solution (with `f = 0`) satisfy `û' = fourierNSField ν û`. The proof differentiates under the integral (`hasDerivAt_coeff_time`), integrates by parts on the unit cell (`cubeCoeff_pdR`), writes the convective term as a convolution (`cubeCoeff_mul_series`, `convective_coeff`) and removes the pressure by the Leray step (`leray_solve`, `fourierNSField_eq_dtCoeff`).
- `periodicFourierCoeffDecay ν : PeriodicFourierCoeffDecay ν`. Both halves are proved:
  - the `û` half comes from `(1 − Δ/4π²)^m` bounds on the compact set `[0,T'] × cell` (`cubeCoeff_helmR`, `jreg_decay`);
  - the `fourierNSField` half applies the same bound to `∂ₜu` and identifies `fourierNSField ν û(t)` with the coefficients of `∂ₜu` on all of `[0,T']` (`dtCoeff_div` extends the divergence constraint to the endpoints by continuity).
- `periodicFourierHsEnergyIdentity ν s : PeriodicFourierHsEnergyIdentity ν s` is now **unconditional**.
- `periodicBKMHsControl_of_commutator_lowFreq` gives BKM `H^s` control, conditional only on `PeriodicFourierCommutatorBound` and `PeriodicLowFreqVorticityBound`.

**Still conditional:** `PeriodicFourierCommutatorBound`, `PeriodicLowFreqVorticityBound`, and `PeriodicBKMIntegrability`, which remains open. **The Clay problem is not solved by this repository, and global regularity for unmodified 3D Navier–Stokes is not claimed.**

Coined names: `liftR`, `pdR`, `PerR`, `PerR.pdR`, `liftR_contDiff`, `liftR_add_single`, `pdC_liftR`, `cubeCoeff_pdR`, `compC_eq_liftR`, `fderiv_coord`, `laplacian_coord`, `convective_coord`, `pressureGradient_coord`, `phase_mul_charK`, `cubeCoeff_mul_series`, `hasDerivAt_coeff_time`, `integrableOn_cube_of_continuous`, `cubeCoeff_sub'`, `cubeCoeff_const_mul'`, `cubeCoeff_sum'`, `perR_coord`, `perR_of`, `PerR.continuous_liftR`, `cubeCoeff_dt_eq`, `norm_cubeCoeff_le`, `convective_coeff`, `leray_solve`, `dtCoeff`, `data_of_sol`, `fourierNSField_eq_dtCoeff`, `dtCoeff_div_Ioo`, `periodicFourierCoeffODE`, `dJ`, `helmR`, `helmJ`, `JReg`, `PerR.helmR`, `cubeCoeff_helmR`, `JReg.slice`, `pdR_slice`, `JReg.dJ`, `JReg.helm`, `helmR_slice`, `JReg.iterate`, `cubeCoeff_iterate_helmJ`, `jreg_decay`, `JReg.continuousOn_coeff`, `jreg_u`, `jreg_dt`, `dtCoeff_div`, `periodicFourierCoeffDecay`, `periodicFourierHsEnergyIdentity`, `periodicBKMHsControl_of_commutator_lowFreq`.

## Parseval (Parseval.lean)

**Proved (no sorry, standard axioms only):**
- `hasSum_prod_cubeCoeff` (Parseval's identity): for continuous `ℤ³`-periodic `f, g : ℝ³ → ℂ`, `Σ_k conj(f̂_k) ĝ_k = ∫_{[0,1]³} conj(f) g`. This is transferred from Mathlib's `hasSum_prod_mFourierCoeff` on `UnitAddTorus (Fin 3)`. It is the first step of the `s = 3` physical-space (Kato–Ponce / Gagliardo–Nirenberg) route to `PeriodicFourierCommutatorBound`.

Coined names, to be renamed later: `torusLift`, `torusLift_mk`, `continuous_torusLift`, `integral_torusLift`, `mFourierCoeff_torusLift`, `hasSum_prod_cubeCoeff` (modelled on Mathlib's `hasSum_prod_mFourierCoeff`).

## Physical-space commutator bound at s = 3 (PhysicalCommutator.lean)

**Proved (no sorry, standard axioms only):**
- `hasSum_rate_three`: for smooth periodic divergence-free `v`, the Fourier-side `H³` nonlinear rate is summable and equals `-2 Σ_i ∫_{[0,1]³} (1 - Δ/4π²)³ v_i · ((v·∇)v)_i`. The proof uses Parseval three times. The pressure (Leray gradient) part drops out because `k · v̂_k = 0`, and its summability is shown directly.
- `periodicFourierCommutatorBound_of_physical`: `PeriodicPhysicalCommutatorBound C → PeriodicFourierCommutatorBound 3 C`.
- `periodicBKMHsControl_of_physical_lowFreq`: `PeriodicPhysicalCommutatorBound C` (with `C ≥ 0`) together with `PeriodicLowFreqVorticityBound` gives `PeriodicBKMHsControl ν 3`.

**FLAG, coined Prop (now proved, see CommutatorAssembly.lean below):** `PeriodicPhysicalCommutatorBound C` says that `-2 Σ_i ∫ (1 - Δ/4π²)³ v_i · ((v·∇)v)_i ≤ C ‖∇v‖_∞ ‖v‖²_{H³}`. This is the classical `s = 3` Kato–Ponce / Gagliardo–Nirenberg energy estimate. It is a sufficient replacement for `PeriodicFourierCommutatorBound 3 C`, and the reduction is proved. It is discharged in CommutatorAssembly.lean.

Coined names, to be renamed later: `PeriodicPhysicalCommutatorBound`, `convR`, `hasSum_rate_three`, `periodicFourierCommutatorBound_of_physical`, `periodicBKMHsControl_of_physical_lowFreq`, `hasSum_mode_fin`, `perR_convR`, `cubeCoeff_convR`, `nlField_eq_convR`, `abs_mul_le_ksq`, `leray_grad_term_bound`, `hasSum_re_cubeCoeff`, `summable_sq_norm_cubeCoeff`, `PerR.add_int`, `PerR.liftR_int`, `PerR.iterate_helmR`, `cubeCoeff_iterate_helmR`.

## Kato–Ponce toolkit (KatoPonce.lean)

Work toward discharging `PeriodicPhysicalCommutatorBound`. (Completed in CommutatorAssembly.lean.)

**Proved (no sorry, standard axioms only):**
- Unit-cell calculus for smooth periodic scalar fields: closure of `PerR` under products, sums and scalar multiples; the Leibniz rule `pdR_mul`; linearity of `pdR`; Schwarz symmetry `pdR_comm`; `∫_{[0,1]³} ∂_j φ = 0` (`cellI_pdR`); and integration by parts (`cellI_ibp`).
- `gagliardoNirenberg_cell` (Gagliardo–Nirenberg): if `|g| ≤ M` then `∫ (∂_a g)⁴ ≤ 9 M² ∫ (∂_a ∂_a g)²`.

Coined names, to be renamed later: `cellI`, `PerR.cont`, `PerR.mul`, `PerR.add`, `PerR.const_mul`, `PerR.sum`, `integrableOn_cell`, `cellI_add`, `cellI_const_mul`, `cellI_neg`, `cellI_sum`, `cellI_mono`, `cellI_nonneg`, `cellI_pdR`, `pdR_mul`, `pdR_add`, `pdR_const_mul`, `pdR_sum`, `pdR_comm`, `cellI_ibp`, `cellI_le_two`, `gagliardoNirenberg_cell`, `cellI_ibp'`, `cellI_sq_mul_abs_le`, `bddAbove_norm_fderiv`, `abs_pdR_coord_le`, `DL`, `PerR.DL`, `DL_append`, `DL_pdR`, `pdR_listSum`, `splits`, `splits_length`, `mem_splits`, `splits_eq`, `DL_mul`, `DL_sum`, `toL`, `exists_toL`, `toL_length`, `physQ`, `le_physQ`, `physQ_nonneg`, `abs_cellI_le`, `lower_term_bound`, `top_term_zero`.

Further proved pieces (KatoPonce.lean): Leibniz rule `DL_mul` for iterated derivatives `DL`; `physQ v` (sum of squared cell integrals of all derivatives of order ≤ 3 of the components); `lower_term_bound` (each lower-order Leibniz term of order-3 commutator is ≤ 5·‖∇v‖∞·physQ, via Gagliardo–Nirenberg); `top_term_zero` (the top-order term vanishes by div v = 0). See below for the assembly.

## Discharging the s = 3 commutator bound (CommutatorAssembly.lean)

All proved; axioms only propext, Classical.choice, Quot.sound.

- `cellI_iterate_helmR`: `∫ (1 - Δ/4π²)ⁿφ · χ` expands as `wordSum n` over derivative words, by repeated integration by parts.
- `word_bound`: for each word `L` of length ≤ 3, `|Σ_i ∫ ∂^L v_i · ∂^L ((v·∇)v)_i| ≤ 315 ‖∇v‖_∞ physQ v`.
- `sum_cellI_helm_three`: `Σ_i ∫ (1 - Δ/4π²)³v_i · v_i = hsSq 3 v` (Parseval).
- `physQ_le_hsSq`: `physQ v ≤ 64 (4π²)³ hsSq 3 v`.
- `periodicPhysicalCommutatorBound`: `PeriodicPhysicalCommutatorBound (2·64·315·64·(4π²)³)`.
- `exists_periodicPhysicalCommutatorBound`: `∃ C, 0 ≤ C ∧ PeriodicPhysicalCommutatorBound C`.
- `periodicBKMHsControl_three_of_lowFreq`: `PeriodicLowFreqVorticityBound → PeriodicBKMHsControl ν 3`. **Conditional only on `PeriodicLowFreqVorticityBound`**, which is not proved.

Nothing here proves `PeriodicBKMIntegrability`, the Clay problem, or global regularity of Navier–Stokes.

Coined names, to be renamed later: `pdR_helmR`, `DL_helmR`, `cellI_helmR_mul`, `wordSum`, `cellI_iterate_helmR`, `wordSum_sum`, `helm_const_le_one`, `helm_const_pos`, `abs_wordSum_le`, `wordSum_nonneg`, `le_wordSum`, `cellI_listSum`, `abs_listSum_le`, `word_bound`, `sum_cellI_helm_three`, `physQ_le_hsSq`, `periodicPhysicalCommutatorBound`, `exists_periodicPhysicalCommutatorBound`, `periodicBKMHsControl_three_of_lowFreq`.

## Toward `PeriodicLowFreqVorticityBound` (LowFreqKernel.lean)

`PeriodicLowFreqVorticityBound` is still an unproved hypothesis. It is a true classical estimate, not a false one, and it is not weakened here. Proved so far:

- `multiplier_eq_conv`: a finitely supported Fourier multiplier applied to `cubeCoeff g` equals convolution of `g` with the trigonometric polynomial `multKernel S m` over the unit cell.
- `norm_multiplier_le`: `L¹ * L^∞` (Young) bound. If `‖g‖ ≤ B` on the cell, the output at `x` is at most `B · ∫_{[0,1]³} ‖K(x−y)‖ dy`.
- `gradCoeff_eq_vort` (BiotSavartCoeff.lean): Fourier-side Biot–Savart. For `k ≠ 0`, `gradCoeff v k i j = −k_j (k × ω̂_k)_i / |k|²`; `gradCoeff_zero` handles `k = 0`.
- `integral_normSq_multKernel` (CellParseval.lean): Parseval for trigonometric polynomials on `[0,1]³`, built on the orthogonality lemma `integral_charE_mul_conj`.
- KernelWeighted.lean (step 2 foundations): `cell_weighted_L1` gives `∫‖K‖ ≤ (∫W⁻²)^{1/2}(∫‖WK‖²)^{1/2}` for any continuous `W ≥ 1`. `cellWeight_mul_multKernel` shows that multiplying by `W_A = 1 + A Σ_l |e(z_l)−1|²` maps coefficients `c` to `c − A·secDiffSum c`. `integral_normSq_multKernel_sub` is translated Parseval.

Remaining plan, not done:
2. Dyadic smooth blocks: show each block kernel has cell `L¹` norm bounded uniformly in the scale. The intended route is weighted Cauchy–Schwarz plus Parseval with second differences of the multiplier.
3. Bound the de la Vallée Poussin kernel in `L¹`.
4. Sum the `O(log R)` blocks.

Coined names, to be renamed later: `charE`, `multKernel`, `continuous_charE`, `continuous_multKernel`, `charE_sub`, `multiplier_eq_conv`, `norm_multiplier_le`, `crossC`, `vortCoeff`, `vort_comp`, `vortCoeff_eq`, `gradCoeff_eq_vort`, `gradCoeff_zero`, `integral_exp_int`, `charE_eq_prod`, `volume_restrict_cell`, `integral_charE`, `charE_mul_conj`, `integral_charE_mul_conj`, `integral_normSq_multKernel`, `memLp_two_cell`, `cell_cauchySchwarz`, `cell_weighted_L1`, `charE_mul_multKernel`, `modeBox`, `mem_modeBox`, `card_modeBox`, `BoxSupp`, `multKernel_mono`, `unitMode`, `boxSupp_shift`, `charE_mul_multKernel_box`, `abs_unitMode`, `multKernel_add`, `multKernel_smul`, `normSq_charE_sub_one`, `secDiffSum`, `cellWeight`, `continuous_cellWeight`, `one_le_cellWeight`, `cellWeight_mul_multKernel`, `norm_charE`, `multKernel_sub_eq_conj`, `integral_normSq_multKernel_sub`.

## Copyright, license and scope

Copyright 2026 Benjamin Stanley Frohman (ORCID [0009-0006-7068-3718](https://orcid.org/0009-0006-7068-3718)). Licensed under the Apache License, Version 2.0; see `LICENSE` and `NOTICE`.

What is proved vs. conditional: Proved steps are listed above; the open step `PeriodicBKMIntegrability` (and any other named `Prop` listed above) remains an explicit hypothesis. Every hypothesis is a named `Prop` passed as an explicit argument. Nothing in this repository claims to solve the Clay Millennium problem or global regularity for unmodified 3D Navier–Stokes.
