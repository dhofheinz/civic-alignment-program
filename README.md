# The Civic Alignment Program

Four papers, three verification batteries, and a Lean 4 formalization on AI deployment
and collective epistemic capacity: the pressure (satisfaction-optimal deference statically degrades capacity on
contested claims), the trap (the coupled operator-population system is bistable, with
capture, hysteresis, and telemetry blindness), the loop (the feedback structure admits
identification and knob-free certification), and the audit (a pre-registered protocol
locating deployments on the pressure-drift-capture ladder). Existing evidence documents
mechanisms consistent with civic misalignment pressure; whether any current deployment
exhibits civic drift or civic capture is an open empirical question -- this program
exists to answer it.

## Papers
- I   -- Civic Alignment: Measuring AI Safety by Collective Epistemic Capacity (arXiv: TBD)
- II  -- Civic Drift: Threshold Dynamics of Satisfaction-Optimized Deference (arXiv: TBD)
- III -- Civic Loops: Regulating the Feedback Structure, Not the Knob (arXiv: TBD)
- IV  -- The Civic Capture Audit: A Pre-Registered Protocol (arXiv: TBD)

## Reproduce
    python --version  # must report Python 3.14.6 (see .python-version)
    python -m venv .venv && source .venv/bin/activate
    python -m pip install --require-hashes -r requirements-lock.txt
    python batteries/derisk_numerics.py   # expect: DE-RISK RESULT: 31/31 suites pass
    python batteries/derisk_loops.py      # expect: LOOPS DE-RISK RESULT: 15/15 suites pass
    python batteries/derisk_audit.py      # expect: AUDIT DE-RISK RESULT: 10/10 suites pass
    python batteries/check_hypotheses.py  # expect: guard #3: GREEN (printed benchmark vs printed hypotheses)
    (cd figures && python make_figures.py && python make_loops_figures.py)

All suites are seed-pinned; every quantitative claim in the papers has a named,
asserted witness in a battery. Last verified from a clean checkout on 2026-08-03
(Python 3.14.6; the complete transitive dependency graph and accepted artifact
hashes are pinned in `requirements-lock.txt`). `requirements.txt` is the short
list of direct constraints used to regenerate that lock with pip-tools 7.6.0.

## Machine-checked proofs (Lean 4)
Formal results of Papers I--III and the registered decision, coverage, causal-obligation,
and clearance core of Paper IV are
formalized in Lean 4 against Mathlib in `lean/`, with zero `sorry` and zero
project-specific axioms: every declaration audits to Lean's three foundational axioms
alone, checkable per declaration via `#print axioms`. As of 2026-08-04, 61 of the 63
labeled results across Papers I--III are proved (Paper I 12/12, Paper II 32/33, Paper III
17/18); the two remaining rows are a conjecture the paper labels as such and a numerical
report. The development includes a self-contained proof of the
planar local stable-manifold theorem, absent from Mathlib, on which the bistability
theorem's local clause rests rather than on a classical import; the full two-sided and
variational Arrhenius laws for first saddle-policy crossing; the genuine basin-exit
stopping time, its finite-horizon variational barrier, and the unconditional mean-rate bracket
between the crossing and basin quasipotentials; and the sharp genuine mean basin-exit law at
the basin quasipotential under the weighted convergent-step condition. The latter proof
combines uniform boundary accessibility, horizon-independent policy matching, compact-core
recurrence, one fixed-dimensional excursion action tail, and a last-home decomposition;
no growing-horizon asymptotic shorthand is used. Quantitative saddle-passage surgery also
gives an exact conditional reduction of the separate fixed-rate crossing-versus-exit
quasipotential conjecture to a named vanishing-continuation property. Under the proposition's
base `(SS)` assumptions alone, the lower endpoint of the genuine mean basin-exit bracket
remains open. We are not aware of a prior machine-checked stable-manifold theorem, or of
a prior machine-checked large-deviations development of Freidlin--Wentzell type, in any
proof assistant (surveyed 2026-08-05: Mathlib and the Isabelle AFP by full-text search;
other systems by literature search). Supporting declarations also
make Paper I's personalization ordering and three-component capacity comparison, Paper II's heterogeneous stock mixture, Paper
III's finite cadence-rate premise and deterministic finite-channel information model,
and Paper IV's eleven-component familywise error interface explicit without asserting
their remaining empirical premises.
Coverage and verification recipes, together with the claim-type vocabulary
separating theorems, model assumptions, statistical assumptions, battery
measurements, population bridges, interpretive prose, and normative claims,
are in `lean/README.md`.

    export PATH="$HOME/.elan/bin:$PATH"
    cd lean && lake exe cache get && lake build   # the cache step downloads several GB of prebuilt Mathlib

## Cite
See CITATION.cff. Release DOI: 10.5281/zenodo.21811398 (Zenodo concept DOI; resolves to the latest release).

## License
Licensing is path-specific; see `LICENSES.md` for the authoritative map. Python
code and general repository documentation/metadata are MIT. The `lean/` tree is
Apache-2.0, following the Lean/Mathlib ecosystem convention. Manuscripts,
bibliographies, rendered PDFs, and rendered paper figures are copyright the
author with all rights reserved; an arXiv license governs only the copy
distributed by arXiv.
