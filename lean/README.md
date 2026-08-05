# Lean 4 formalization — Civic Alignment Program

Machine-checked proofs for formal results of Papers I–III, together with the
registered decision, tier, and clearance core of Paper IV. Every theorem in
this directory re-checks under the Lean kernel; nothing depends on trusting the author, the
tactics, or any reviewer.

## What this establishes, and what it does not

**It checks inference chains.** For every theorem here, the argument from its
stated hypotheses to its conclusion has been verified by the Lean kernel,
with no project-specific axioms: every declaration audits to Lean's three
foundational axioms (`propext`, `Classical.choice`, `Quot.sound`) and
nothing else — see Assumptions below for the mechanical check.

**It says nothing about whether the models describe any real deployment.** The
papers scope themselves to a deliberately minimal model isolating one
sufficient mechanism; that limit is theirs, and nothing here narrows or
repairs it. A machine-checked proof that satisfaction-optimal deference
degrades a *modelled* capacity is not evidence that any deployed system
behaves that way.

**The verification batteries are out of scope.** The seed-pinned suites in
`../batteries/` report estimator error rates, fitted slopes, out-of-sample
counts, and false-certification rates. None of those claims is formalized
here, and none is made more true by this development. The finite-sample
Chebyshev and Bonferroni theorems below are distribution-free implications
under their own explicit unbiasedness, true-variance, and marginal-budget
hypotheses; they do not formalize the batteries' estimated-SE frequencies.

**No paper is "verified," and not every printed claim is a theorem.** Papers
I–III contain assumptions, remarks, empirical citations, and interpretive
prose that no formalization addresses. Of the 63 labeled formal results
in Papers I–III, 61 are proved; `conj:arr` remains open because the paper
states it as a conjecture; and `prop:id` reports battery measurements rather
than a theorem (its exact algebraic core is proved). The precise claim for any single result is mechanical:
`#print axioms CivicAlignment.<name>` shows exactly what it rests on.

**Every printed claim has exactly one evidentiary type.** The papers'
Verification sections apply a fixed cross-paper vocabulary for what kind of
support a claim has:

| Type | Meaning |
|---|---|
| `FORMAL` | A mathematical implication with explicit hypotheses, checked here in Lean. |
| `MODEL` | A primitive, definition, or maintained model assumption. It is not asserted as deployment truth. |
| `STAT-ASSUMPTION` | A sampling, coverage, asymptotic, or causal-identification premise required for statistical transfer. |
| `BATTERY` | A seed-pinned measurement under a specified simulation law. It is descriptive of that experiment only. |
| `EXTERNAL-EMPIRICAL` | A claim about observed systems or people supported by cited empirical work. |
| `POPULATION-BRIDGE` | A construct-validity or transport implication from an audited estimand to a scoped population proposition. |
| `INTERPRETIVE` | A conceptual, information-theoretic, economic, or regulatory reading of formal results. |
| `NORMATIVE` | A proposed objective, threshold, reporting rule, or governance choice. |
| `OPEN` | A precise mathematical or empirical obligation not discharged in the current tree. |

The governing rule is conservative and one-directional: Lean checks
implications only. Battery frequencies do not prove probabilities outside
their simulation law; cited evidence does not prove a population bridge; and
a registered decision does not make its coverage event true. Evidence of one
type never promotes a claim of another.

## Coverage highlights

**Paper I is complete.** Every labeled formal result is proved — the lemma
chain, the main theorem, the manipulability closed forms, the civic-weighted
incentive proposition, and the finite-corpus lift. The latter proves the exact
finite-sum derivative identity and the strict pooled-capacity conclusion, and
makes explicit that a positive share of harmful claims alone does not sign
the pooled derivative when outside-claim slopes are unrestricted. The
same-side counterexample of `rem:counter` shows the contested-claim assumption
is necessary rather than decorative. All of it audits to Lean's three
foundational axioms alone.

**Paper I's personalization comparative static and capacity comparison are
explicit.** `Personalization.lean` proves that pointwise derivative dominance
orders two interior local maximizers when the low-type utility is
differentiable and strictly concave (and records the weaker first-order-sign
theorem actually used). It then defines all three capacity-loss terms with
separate high- and low-type policy inputs and proves that moving only the
low-type choice weakly rightward worsens population accuracy loss, within-type
dispersion, and squared between-type separation relative to applying the
high-type choice globally; personalized capacity is therefore weakly lower.

**Paper II's bistability theorem is complete, including the stable
manifold.** Lean proves the fixed-point catalogue, corner traps, exact saddle
spectrum, monotone-step and `(SS+)` convergence, the stable-set antichain and
empty interior, disjoint open basins with common boundary, and the exact
period-two sharpness witness — and the local `C¹` stable-arc clause is proved
from scratch: Irwin's planar
stable-manifold theorem, built on Mathlib's implicit function theorem over
the Banach space of bounded sequences, instantiated at the saddle through the
explicit eigenbasis, and matched to the ambient stable set by the internally
proved antichain and quadrant-exclusion order structure. Mathlib itself
carries no stable-manifold theorem; the self-contained development is in
`PaperII/NemytskiiSubstitution.lean` through `PaperII/StableManifold.lean`.

**Paper II's hysteresis theorem is complete.** The formal schedule
distinguishes prevention, release, and restoration; proves the policy-uniform
prevention trap, exact release threshold, weighted restoration convergence on
the invariant box, and stable descending crossings; and leaves the release
equality case undetermined exactly as the paper does. Exact rational checks
give `0.0162 < 0.0245` and `rho_restore = rho_cure = 2/25 = 0.0800` at the
benchmark.

**Paper II's first-crossing Arrhenius laws are complete.** The canonical
product-Gaussian chain has an honest stopping time and extended mean time to
first saddle-policy crossing. Lean proves persistence below the crossing
quasipotential, crossing above it, exact convergence of
`sigma^2 log E[T_x]` to that variational value, the printed two-sided
closed-form bracket, and the fixed-primitives small-adaptation-rate limit. The
persistence proof prices the first near-saddle-strip entrance after the last
home exit, placing every arbitrary-duration excursion inside one
fixed-dimensional action tail; no saddle-sojourn assumption or external
dynamical-systems theorem is used.

**Paper II's genuine basin-exit rate has an unconditional variational
bracket and a sharp weighted-regime law.** `BasinExitProcess.lean` proves that the weighted calibrated basin is
relatively open, defines its measurable first-exit stopping time, and shows
that every finite exit pays the basin quasipotential `V`. A standalone compact
recurrence theorem prices long excursions by an exact linear block-action
charge, with no growing-horizon shorthand. Independently, the basin's lower-set geometry makes one
finite exit control from the calibrated corner a uniform exit certificate
from every reachable restart state. The finite Gaussian product restart,
geometric survival estimate, exact tail-sum identity, and one-sided control-box
rate then prove
`limsup sigma^2 log E[tau_B] <= V`. Together with the first-crossing comparison,
`BasinExitLaw.lean` proves the unconditional bracket
`V^x <= liminf <= limsup <= V`. Under
`HasVanishingSaddlePassageContinuation`, the two endpoints agree and Lean
proves convergence of the genuine mean-exit rate to `V`. Independently, under
the weighted convergent-step condition, `BasinExitLower.lean` proves the same
sharp law directly, without identifying `V^x` and `V`. Excursions on every
positive-clearance compact core are charged linearly
(`BasinExitRecurrence.lean`, on the generic `LowActionRecurrence` engine), and
the boundary geometry is closed in `BasinBoundaryAccessibility.lean`: every relative boundary
orbit converges to the weighted saddle; an explicit two-step push exits from a
whole saddle neighborhood with action tending to zero; compactness supplies a
uniform positive inner-layer width and common maximum horizon; and
`quasipotential_le_action_add_of_terminal_in_boundaryLayer` proves that any
controlled prefix reaching that layer already costs at least `V - epsilon`.
Policy matching transports that charge uniformly to every start in a home
ball with an error independent of path length. The first target entrance then
has a dichotomy: a short excursion pays the transported boundary charge, while
a long excursion pays enough fixed core blocks. Thus every completed excursion,
regardless of duration, lies in one fixed-dimensional Gaussian action tail at
`V - epsilon`. A last-home union bound gives persistence through
`floor(exp((V - delta) / sigma^2))`; the elementary survival-to-expectation
bound and the existing upper theorem give
`sigma^2 log E[tau_B] -> V`. No infinite length-class sum is needed. Without
weighted `(SS+)`, global convergence of boundary orbits is unavailable, so the
lower upgrade from `V^x` to `V` under the proposition's base `(SS)` assumptions
remains open.

**Paper II's stock-law robustness is now partly nonlinear-theorem-grade.** A
generic monotone planar theorem (`nonlinear_global_bistability`) proves
invariant-rectangle confinement, cooperativity, exactly three ordered
equilibria under an explicit crossing condition, comparable-tail convergence,
and global convergence to one of the three, from abstract step bounds.
`affine_global_bistability_via_nonlinear_robustness` rederives the affine
global-convergence clause as a specialization without changing any affine
definition or hypothesis, and `groundedSqrt_global_bistability` instantiates
the same theorem for the grounded square-root family
`D' = (m(β)√D + j)²` with `m(β) = √(1−λ₀)·(1−η(1−β))`, whose squared
deviation persists at exactly `1−λ₀` per period. The nonlinear route covers
global convergence and the equilibrium catalogue only: hyperbolicity, the
`C¹` stable arc, and the basin topology remain affine-law theorems, and the
grounded family's crossing/step hypotheses are maintained restrictions until
a parameter witness is registered.

**Paper II's quantitative-passage proposition is complete in its uniform
small-rate form.** The proposition fixes every primitive except the adaptation
rate. Lean proves the exact transport and sign-free hold formulas, the
margin-two rate ceiling, complete deficit-plus-retreat ledgers, and finite
burden-aware Selection. The surgery truncates before the selected advancing
cell, retains the whole suffix refund and exact residual square, and exits by
one natural margin climb plus a sign-free hold; normal and overleaping cells
are treated separately. The local `O(w²)` estimate uses the displayed
logarithmic factor only through its lower bound of one and yields
`quantitativeSaddlePassage_uniform` with one constant uniform over all
sufficiently small positive rates. A fixed-rate variant
(`quantitativeSaddlePassage_logPlus`) is stated separately with its
positivity hypothesis explicit.

**Paper II's remaining fixed-rate saddle-passage obligation is exact.**
`HasVanishingSaddlePassageContinuation` asks, at every positive tolerance,
for a near-minimal prefix ending strictly above the saddle whose exact
sign-free squared-lag continuation price is below the same tolerance. Lean
proves that this property implies `V^x = V` in
`saddlePassageConjecture_of_vanishingContinuation`; it does not assert the
property. This is the precise open variational selection/continuity step, not
an unproved use of the already-established finite hold formula.

**Paper II's reverse-passage spectrum is a diagnostic, not an equality
criterion.** `ReversePassageSpectrum.lean` proves the exact reverse-map
Jacobian and its quadratic-in-rate discriminant, and partitions fixed-rate
configurations into real-mode and oscillatory-mode regimes by its sign. It
does not infer either quasipotential from that local spectrum. Stable-manifold
optimization across the sign change finds no onset of a positive
`V - V^x` gap; exact fixed-rate equality remains the separate continuation
obligation above.

**Paper II's heterogeneous stock aggregation is exact.**
`HeterogeneousStock.lean` proves that the aggregate contraction is the current
stock-share-weighted mixture of the typewise squared contractions. The factor
is state-dependent in general. A constant representative factor is recovered
exactly under homogeneous evidence weights or a fixed registered type-stock
mixture, including the grounding-and-arrivals conditional-mean law.

**Paper II's registered finite harm Gini is defined.**
`HarmIncidenceSummary.lean` requires nonnegative normalized type weights and
nonnegative marginal harms, fixes the zero-mean convention, and proves
nonnegativity, the constant-curve zero result, and the zero-mean criterion
under strictly positive weights. A continuous Lorenz/quantile construction is
not asserted.

**Paper III's certificate and network results are complete**, including the
knob-free certificate with its projected-gradient, fixed-sign, and
multiplicative instances, and the network certificate with the full
bounded-stock / injection-series / spectral-radius equivalence, proved
through honest complexification and Gelfand's formula with no Perron import.

**Paper III's five-parameter margin geometry is explicit.** Lean proves the
exact perturbation identity for jointly estimated
`(v,c,lambda₀,g,I₀)`, nonnegativity of the full gradient–covariance–gradient
form under positive semidefiniteness, and equality with the diagonal shortcut
under the precise zero-off-diagonal hypothesis. No independence shortcut is
built into the full definition. It also proves the exact safe-side implication
on any supplied coverage event and a non-asymptotic linear-plus-bilinear
remainder radius for finite five-coordinate perturbations. Choosing twice an
estimated standard error as that radius remains an asymptotic statistical
calibration, not an algebraic consequence.

**Paper III's finite-sample identification and coverage boundaries are
explicit.** Arbitrary additive moment errors give exact estimator-error
identities: retirement error divided by exposure, response and content-gain
error contrasts divided by their registered design spreads, the matching
intercept leverage term, and a deterministic fixed-`(v,c)` margin envelope.
For an unbiased square-integrable scalar margin estimator with positive true
variance, Chebyshev bounds coverage failure and false certification at any
positive fixed radius; two true standard deviations give the distribution-free
`1/4` bound. For a finite family, Lean proves the joint failure bound by the
sum of marginal budgets and transfers it to any false composite verdict
contained in that failure union, without independence. None of these results
asserts unbiasedness, supplies true variances, validates estimated standard
errors, or discharges construct validity in a deployment.

**The projection calculus is stated once.** `lem:clip` (`ClippedStep.lean`)
proves, for a general compact interval, the four consequences of the policy and
belief projections used throughout Papers II--III: order and `1`-Lipschitz
transfer, the deadzone (a strict inequality survives only where the clip is
inactive, and a raw rate `1-k` becomes `max{0,1-k}`), face absorption, and
non-injectivity. Every consumer site is wired to it.

**Paper III's rate-separation chain is closed at theorem level.** The jump-map
conjugacy and projected limit are exact; the fixed-horizon error has an
explicit `Cₙ|α|` bound, sharpened to one horizon-independent
`C|α|n` estimate. For positive initial rescaled excess, Lean defines the
projected stopping horizon
`ceil(log(E₀/ε)/log(1/(1-λ₀+g)))`, proves the projected excess is at most
`ε` there, and proves a uniform `C|α|(1+log(E₀/ε)/log(1/(1-λ₀+g)))`
error at every earlier time. An explicit joint-range corollary transfers entry
below `ε` to the exact rescaled orbit by running the projected orbit to
`ε/2`. The raw map is recovered under the precise
`RawJumpTransit` condition; characteristic capture and the sub-saddle trap
hold with the paper's full quantifiers; the burn-limit
trichotomy is continuous; and the two-sided separatrix limit is proved.

**Finite cadence claims now have an exact missing-premise interface.**
`CadenceRate.lean` proves that a supplied error bound on
`α(D_sep-D*)-κ*` gives an explicit inverse-cadence interval at that operating
rate and a quantitative error around exact doubling when cadence is halved.
`SeparatrixRateCertificate` packages the uniform rate estimate required to
invoke those results. The nonlinear dynamics do not yet supply that
certificate, so the small-rate limit has not silently become a finite-rate
identity.

**Paper III's detection latency is exact.** Lean defines the first-alarm
candidate as
`ceil(log((Rε + |x̄|) / |x₀ - x̄|) / log(1 + ζ))`, proves that it is the
minimal integer alarm time on the stated small-weight range, and brackets its
difference from the paper's continuous leading term between the named affine
offset and that offset plus one. The offset is nonnegative and at most
`log 2 / log(1 + ζ)` on the same range. Only the fitted battery slope and
regression statistics remain empirical.

**The captured-face “zero bits” reading has an explicit finite model.** For a
finite prior on hidden low-coordinate states and any finite quantization of a
deterministic satisfaction sensor, `DeterministicInformation.lean` defines
the deterministic-channel mutual information as output Shannon entropy and
proves it is zero from the exact captured-face output invariance. This does
not assert a continuous differential-entropy or noisy-channel theorem.

**Paper IV's registered protocol core is explicit and conditional.** Lean
separates the population predicates for pressure, drift, and capture from the
five audit decision events; in particular, captured-side basin membership is
not the full capture predicate. Registered primitive tests return positive,
negative, or abstain; condition conjunctions and the strongest-tier function
preserve earned lower tiers while proving that no partial set licenses a
higher one. Audit records carry an explicit deployment/domain/stream/envelope
scope. C4-prime and clearance are supplementary outputs that cannot alter the
tier, and positive clearance is sound on its stated margin-coverage event and
certificate-model bridge. At primitive-instrument grain, seven scalar coverage
events, four non-scalar positive-side classification events, and six named
scoped population bridges are separate inputs; supplying all three constructs
the abstract identification record and makes the returned tier sound.
`RegisteredCoverage.lean` indexes all eleven primitive failure opportunities
and transfers supplied marginal budgets to a registered familywise cap with
no independence assumption; for a random audit it also proves automatically
that any overstated returned tier lies in that failure union whenever the
construct bridges hold. `BasinClassification.lean` decomposes a fitted signed
basin score into map-fit, envelope, and state-estimation errors and transfers
their supplied marginal bounds to a false-positive risk bound.
`CausalIdentification.lean` types intervention
fidelity, consistency, temporal stability, observability, and exclusion for
the pulse classifier, and exchangeability, positivity, nuisance validity,
registered censoring time, retained measurement, and uncertainty propagation
for the survivorship design. C4-prime retains the same separation between
contrast coverage and its capturability model bridge. Every calibration,
classification event, causal premise, and population bridge remains an
empirical obligation, not a consequence of the decision algebra.

**What remains unproved or outside theorem scope.** `conj:arr` is open by
design: its exact proposition is `saddlePassageConjecture`, and the sufficient
continuity premise isolated above remains unproved. `prop:id`'s finite-panel recovery errors and fitted rates, the
probability of the estimated-SE/asymptotic-normal coverage event and the battery-count
portions of `prop:safe`, and all other
estimator error rates, fitted slopes, out-of-sample counts, and
false-certification rates remain empirical. Their algebraic cores are
machine-checked where the papers state exact identities; their measurements
are not. Paper IV's coverage assumptions, hard-decision validity, causal and
construct bridges, and deployment transport likewise remain empirical
obligations. The claim-type vocabulary above fixes what kind of support each
such item has; each paper's Verification section states its own boundary.

## Coverage ledger

The 63 labeled formal results of Papers I–III and the Lean declaration each
one names. Declarations live under the `CivicAlignment` namespace; audit any
row with `#print axioms CivicAlignment.<name>`.

| Paper | Label | Declaration (`CivicAlignment.*`) | Status |
|---|---|---|---|
| I | `obs:gamma` | `PaperI.gamma_geometry` | proved |
| I | `lem:decomp` | `PaperI.mse_decomposition` | proved |
| I | `lem:mse` | `PaperI.mse_monotonicity` | proved |
| I | `lem:within` | `PaperI.within_fragmentation_monotonicity` | proved |
| I | `lem:gap` | `PaperI.stratification_gap_widens` | proved |
| I | `cor:totalvar` | `PaperI.total_variance_increases` | proved |
| I | `thm:main` | `PaperI.satisfaction_optimal_deference_harms` | proved |
| I | `prop:closed` | `PaperI.manipulabilityGradient_closedForm` | proved |
| I | `prop:baseline` | `PaperI.manipulabilityGradient_baseline` | proved |
| I | `cor:mgsign` | `PaperI.manipulabilityGradient_baseline_sign` | proved |
| I | `prop:incentive` | `PaperI.civicWeighted_objectives_restore_safe_corner` | proved |
| I | `prop:corpus` | `PaperI.hasDerivAt_pooledCorpusCapacity`; `PaperI.pooledCorpusCapacitySlope_neg`; `PaperI.pooledCorpusCapacitySlope_eq_subset_add_complement`; `PaperI.pooledCorpusCapacitySlope_neg_iff_subset_add_complement_neg`; `PaperI.pooledCorpusCapacity_strictAntiOn` | proved |
| II | `lem:agg` | `PaperII.aggregateAgreement` | proved |
| II | `lem:ratchet` | `PaperII.ratchet` | proved |
| II | `lem:manu` | `PaperII.manufacture` | proved |
| II | `lem:knife` | `PaperII.satisfactionConservation` | proved |
| II | `prop:myopia` | `PaperII.myopiaTrap` | proved |
| II | `lem:clip` | `clippedStep` | proved |
| II | `lem:box` | `PaperII.ceilingBox_absorbing` | proved |
| II | `lem:mono` | `PaperII.loopMap_monotoneOn_box` | proved |
| II | `lem:root` | `PaperII.thresholdAutomatic` | proved |
| II | `thm:bistable` | `PaperII.bistability` | proved |
| II | `thm:hyst` | `PaperII.hysteresisAsymmetry` | proved |
| II | `prop:qpbounds` | `PaperII.civicQuasipotential_lower_bound` | proved |
| II | `cor:qplimit` | `PaperII.smallRateQuasipotentialLimit` | proved |
| II | `prop:arrwindow` | `PaperII.escapeProbabilityWindow` | proved |
| II | `thm:arr` | `PaperII.arrheniusLaw` | proved |
| II | `thm:rate` | `PaperII.escapeRateVariational` | proved |
| II | `prop:basinexitprocess` | `PaperII.civicWeightedCalibratedBasinInBox_isOpen`; `PaperII.gaussianBasinExitTime_isStoppingTime`; `PaperII.gaussianEscapeTime_le_gaussianBasinExitTime`; `PaperII.gaussianBasinExitLogRate_limsup_le_quasipotential`; `PaperII.meanGaussianBasinExitLogRate_bracket`; under weighted `(SS+)`, `PaperII.hasUniformVanishingBasinBoundaryAccessibility_of_convergentStep`, `PaperII.quasipotential_le_action_add_of_terminal_in_boundaryLayer`, `PaperII.basinExitLowerProbability_of_convergentStep`, `PaperII.basinExitLowerMeanRate_of_convergentStep`, and `PaperII.meanGaussianBasinExitLogRate_tendsto_of_convergentStep`; conditional base-regime law `PaperII.meanGaussianBasinExitLogRate_tendsto_of_vanishingContinuation` | proved |
| II | `prop:passage` | `PaperII.quantitativeSaddlePassage_uniform` | proved |
| II | `lem:saddlehold` | `PaperII.cancellingHoldAction_at_saddle_eq_price_sub_tail`; `PaperII.tendsto_cancellingHoldAction_at_saddle` | proved |
| II | `lem:reversepassage` | `PaperII.weightedReversePassageJacobian_discriminant`; `PaperII.reversePassageDiscriminantAtRate_eq_quadratic`; `PaperII.reversePassage_nodal_or_oscillatory` | proved |
| II | `conj:arr` | `PaperII.saddlePassageConjecture`; conditional reduction `PaperII.saddlePassageConjecture_of_vanishingContinuation` | open (conjecture) |
| II | `prop:warning` | `PaperII.earlyWarningNearFold` | proved |
| II | `thm:launder` | `PaperII.satisfactionCapacityDecoupling` | proved |
| II | `cor:sat` | `PaperII.boundedBeliefsSaturation` | proved |
| II | `lem:affine` | `PaperII.affineMeanDynamics` | proved |
| II | `prop:quad` | `PaperII.stratificationExplicitQuadratic` | proved |
| II | `prop:suff` | `PaperII.contestedClaimSufficientConditions` | proved |
| II | `thm:contA` | `PaperII.continuousTypeHarm` | proved |
| II | `thm:horizon` | `PaperII.horizonDichotomy` | proved |
| II | `prop:bstar` | `PaperII.accuracyOptimalDeferenceUnderRepetition` | proved |
| II | `cor:bands` | `PaperII.inversionBands` | proved |
| II | `prop:ar1` | `PaperII.noisyEvidenceAtStationarity` | proved |
| II | `lem:license` | `PaperII.exactAggregationUnderHomogeneousExtraction`; `PaperII.exactAggregationUnderHeterogeneousExtraction` | proved |
| III | `thm:classify` | `PaperIII.globalConvergence_of_nonnegative_stock` | proved |
| III | `thm:conservation` | `PaperIII.aggregationConservation` | proved |
| III | `lem:bound` | `PaperIII.stock_upper_bound` | proved |
| III | `thm:cert` | `PaperIII.knobFreeCertificate` | proved |
| III | `cor:strict` | `PaperIII.strictMarginCertificate` | proved |
| III | `thm:zones` | `PaperIII.strictCalibrationZone_globalCalibration` | proved |
| III | `prop:ceiling` | `PaperIII.gainCeilings` | proved |
| III | `thm:network` | `PaperIII.networkCertificateForward` | proved |
| III | `thm:exact` | `PaperIII.exactNonlinearIndistinguishability` | proved |
| III | `cor:kalman` | `PaperIII.kalmanObservabilityRanks` | proved |
| III | `prop:latency` | `PaperIII.detectionLatency`; `PaperIII.detectionLatency_exact` | proved |
| III | `thm:jump` | `PaperIII.rescaledFullLoopOrbit_tendsto_projectedJumpOrbit`; `PaperIII.rescaledFullLoopOrbit_error_le_logTransit` | proved |
| III | `lem:charcap` | `PaperIII.characteristicCapture` | proved |
| III | `prop:burn` | `PaperIII.burnPolicyLimit_trichotomy` | proved |
| III | `lem:trap` | `PaperIII.subSaddleTrap` | proved |
| III | `prop:seplimit` | `PaperIII.separatrixScaleLimit` | proved |
| III | `prop:id` | `PaperIII.identificationAlgebra` | battery report (algebraic core proved) |
| III | `prop:safe` | `PaperIII.safeSideMarginVariance` | proved |

Additional supporting declarations, not additional labeled-result rows in
the Papers I–III count:

- Paper III finite-sample identification:
  `PaperIII.retirementRate_add_error_sub`,
  `PaperIII.identifiedResponsiveness_add_errors_sub`,
  `PaperIII.identifiedContentGain_add_errors_sub`,
  `PaperIII.identifiedBaselineArrival_add_errors_sub`,
  `PaperIII.identifiedResponsiveness_error_le`,
  `PaperIII.identifiedContentGain_error_le`,
  `PaperIII.estimatedCertificateMargin_error_le`, and
  `PaperIII.finiteSampleIdentification` (proved).
- Paper III five-parameter margin extension:
  `PaperIII.fiveParameterMargin_increment_exact`,
  `PaperIII.fiveParameterSafeSideCertificate_sound`,
  `PaperIII.fiveParameterLinearRemainder_isCoverageRadius`,
  `PaperIII.fiveParameterSafeSide_of_linearRemainder`,
  `PaperIII.fiveParameterDeltaVariance_nonneg`, and
  `PaperIII.fiveParameterDeltaVariance_eq_diagonal_of_offDiagonal_zero`
  (proved).
- Paper III finite-sample probability transfer:
  `PaperIII.marginCoverageFailureProbability_le_variance`,
  `PaperIII.falseCertificationProbability_le_variance`,
  `PaperIII.twoTrueSigmaCoverageFailureProbability_le_quarter`,
  `PaperIII.twoTrueSigmaFalseCertificationProbability_le_quarter`,
  `PaperIII.finiteFamilyCoverageFailureProbability_le_sum`,
  `PaperIII.finiteFamilyMarginCoverageFailureProbability_le_sumVariance`, and
  `PaperIII.falseVerdictProbability_le_sum_of_subset_failures` (proved under
  their displayed statistical hypotheses).
- Paper I personalization ordering:
  `PaperI.chosenDeference_order_of_firstOrderSigns`,
  `PaperI.personalizedInteriorMaximizer_order`, and
  `PaperI.chosenDeferenceGap_nonnegative`,
  `PaperI.personalizedMeanGap_sub_global`, and
  `PaperI.personalization_amplifies_capacityLossComponents` (proved under the
  displayed maintained assumptions and unit-interval choice ordering).
- Paper II heterogeneous-stock aggregation:
  `PaperII.heterogeneousContractedStock_eq_effective_mul`,
  `PaperII.heterogeneousExpectedNextStock_eq_effective`,
  `PaperII.heterogeneousContractedStock_eq_of_homogeneousWeight`, and
  `PaperII.heterogeneousContractedStock_fixedMixture` (proved).
- Paper II finite harm-incidence summary:
  `PaperII.weightedMeanHarm_nonnegative`,
  `PaperII.pairwiseHarmDifference_nonnegative`,
  `PaperII.finiteHarmGini_nonnegative`,
  `PaperII.finiteHarmGini_eq_zero_of_constant`, and
  `PaperII.weightedMeanHarm_eq_zero_iff` (proved under the displayed finite
  weight and sign conditions).
- Paper III finite cadence-rate transfer and deterministic information:
  `PaperIII.separatrixGap_bounds_of_scaled_error`,
  `PaperIII.separatrixGap_halving_error`,
  `PaperIII.SeparatrixRateCertificate.gap_bounds`, and
  `PaperIII.capturedSatisfaction_zero_deterministic_information` (proved under
  their displayed rate-certificate / finite deterministic-channel models).
- Paper IV canonical tier predicates and identification bridge:
  `PaperIV.CivicPressure`, `PaperIV.CivicDrift`, `PaperIV.CivicCapture`,
  `PaperIV.pressureVerdict_sound`, `PaperIV.driftVerdict_sound`, and
  `PaperIV.captureVerdict_sound` (defined / proved).
- Paper IV registered protocol and clearance:
  `PaperIV.RegisteredOneSidedTest.decision`,
  `PaperIV.RegisteredConditionTests.decisions`,
  `PaperIV.RegisteredConditionDecisions.licensedTier`,
  `PaperIV.no_capture_without_full_gate`,
  `PaperIV.no_drift_or_capture_without_drift_gate`,
  `PaperIV.licensedPressure_sound`, `PaperIV.licensedDrift_sound`,
  `PaperIV.licensedCapture_sound`, `PaperIV.registeredClearance_sound`, and
  `PaperIV.tier_independent_of_supplementary` (defined / proved).
- Paper IV primitive coverage and scoped empirical-bridge composition:
  `PaperIV.RegisteredOneSidedTest.positiveTruth_of_coverage`,
  `PaperIV.registeredC4Prime_sound`,
  `PaperIV.registeredAuditIdentification_of_coverage_and_bridges`,
  `PaperIV.registeredLicensedPressure_scoped_sound`,
  `PaperIV.registeredLicensedDrift_scoped_sound`, and
  `PaperIV.registeredLicensedCapture_scoped_sound` (proved conditionally; the
  coverage records and population/model bridges are not asserted).
- Paper IV non-scalar, familywise, and causal interfaces:
  `PaperIV.RegisteredNonScalarCoverageEvents`,
  `PaperIV.registeredFamilywiseFailureProbability_le_cap`,
  `PaperIV.registeredFalseVerdictProbability_le_cap`,
  `PaperIV.registeredFalseReturnedTier_subset_failureUnion`,
  `PaperIV.registeredFalseReturnedTierProbability_le_cap`,
  `PaperIV.basinScore_coverage_of_component_bounds`,
  `PaperIV.basinClassificationFalsePositiveProbability_le_sum`,
  `PaperIV.pulseBasin_positive_implies_truth`,
  `PaperIV.pulseBasin_nonScalarCoverage`,
  `PaperIV.retentionDesignValid_of_survivorshipAssumptions`, and
  `PaperIV.retention_nonScalarCoverage` (defined / proved conditionally; no
  classification probability or causal premise is asserted).

## Assumptions

There are no project-specific axioms. Every declaration audits to
`propext`, `Classical.choice`, and `Quot.sound` only, and the tree contains
no `sorry` and no `axiom`. All three facts are mechanically checkable:
`#print axioms` per declaration, and `grep -rn "sorry\|^axiom"` over
`CivicAlignment/`.

Three classical results that a development of this kind might be expected
to import are not needed. The **local stable-manifold theorem** at the interior
saddle (Hirsch–Smith 2006; Kuznetsov 2004) is proved from scratch, Mathlib
carrying no such theorem: Irwin's argument solves the orbit equation on the
Banach space of bounded sequences with a hyperbolic Green operator, the
implicit function theorem yields the local `C¹` solution curve tangent to
the contracting eigendirection together with its local uniqueness, and the
internally proved antichain and quadrant-exclusion structure identifies the
ambient stable set with the staying set, closing the gap that in general
separates the two (the module path `Imported/LocalStableManifold.lean` is
historical; its declaration is an ordinary theorem). **Planar cooperative
convergence** (Smith; Hirsch–Smith) is not used: its orientation hypothesis
is unavailable for this map, whose clipped policy projection is not
injective, and the papers instead prove convergence under the stronger
`(SS+)` condition by a self-contained quadrant argument that is formalized
here. **Perron–Frobenius** is not used: strict positivity of the injection
promotes coordinatewise boundedness to summability of the full matrix-power
series, and complexification plus Gelfand's formula closes the spectral
equivalence.

## Sharpness

Several hypotheses in the papers are necessary rather than conventional, and
the development carries machine-checked witnesses to that effect.

- **Cooperativity does not imply convergence.** An exact rational
  parameterization satisfying every primitive restriction, the cooperativity
  condition `(SS)`, and the threshold structure admits a period-two orbit
  inside the invariant box. Convergence holds below an explicit bound on the
  adaptation rate, which is therefore a bifurcation axis rather than a
  nuisance parameter.
- **The certificate margin must be strict where policy coverage is claimed.**
  At a sharp margin the satisfaction gradient can vanish at low deference,
  admitting adaptation rules that leave the certified class; a strictly
  positive margin makes the gradient uniformly one-signed on the whole knob
  range.
- **The invariant box is not absorbing.** A captured trajectory starting
  above the stationary ceiling remains strictly above it at every finite
  time; absorption holds for the enlarged box whose ceiling is the level at
  which monotonicity binds.
- **The jump-map limit inherits policy clipping.** The exact rescaled full
  loop converges at each fixed horizon to a projected jump map; the raw map
  is recovered only while every compared jump remains in `[0,1]`, and an
  overshooting raw step is provably different from the literal limit.
- **Endpoint nondegeneracies are real.** Exact trajectories witness the
  printed qualifications of the laundering and saturation results: persistent
  high injection without policy-sensitive extraction need not give finite
  capture, and clipping shifts the captured satisfaction limit when the
  unbounded fixed point lies outside the state space.

## Building

```
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get      # prebuilt Mathlib oleans — do not skip
lake build
```

Do not run `lake update`. Mathlib is pinned to a tag deliberately, and
`lake-manifest.json` is authoritative.

## License

This directory is Apache-2.0 (see `LICENSE`), following Lean/Mathlib
ecosystem convention so that generally useful lemmas can be contributed
upstream to Mathlib without relicensing. Licensing elsewhere in the repository
is path-specific; see `../LICENSES.md`.
