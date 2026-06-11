# The Civic Alignment Program

Four papers and three verification batteries on AI deployment and collective epistemic
capacity: the pressure (satisfaction-optimal deference statically degrades capacity on
contested claims), the trap (the coupled operator-population system is bistable, with
capture, hysteresis, and telemetry blindness), the loop (the feedback structure admits
identification and knob-free certification), and the audit (a pre-registered protocol
locating deployments on the pressure-drift-capture ladder). Existing evidence
establishes civic misalignment pressure; whether any current deployment exhibits civic
drift or civic capture is an open empirical question -- this program exists to answer it.

## Papers
- I   -- Civic Alignment: Measuring AI Safety by Collective Epistemic Capacity (arXiv: TBD)
- II  -- Civic Drift: Threshold Dynamics of Satisfaction-Optimized Deference (arXiv: TBD)
- III -- Civic Loops: Regulating the Feedback Structure, Not the Knob (arXiv: TBD)
- IV  -- The Civic Capture Audit: A Pre-Registered Protocol (arXiv: TBD)

## Reproduce
    python -m venv .venv && source .venv/bin/activate
    pip install -r requirements.txt
    python batteries/derisk_numerics.py   # expect: DE-RISK RESULT: 29/29 suites pass
    python batteries/derisk_loops.py      # expect: LOOPS DE-RISK RESULT: 14/14 suites pass
    python batteries/derisk_audit.py      # expect: AUDIT DE-RISK RESULT: 10/10 suites pass
    python figures/make_figures.py && python figures/make_loops_figures.py

All suites are seed-pinned; every quantitative claim in the manuscripts has a named,
asserted witness in a battery. Last verified from a clean checkout on 2026-06-11
(Python 3.10, dependency versions as pinned in requirements.txt).

## Cite
See CITATION.cff. Release DOI: TBD (Zenodo, on first tagged release).

## License
MIT (code). Manuscripts (c) the author; preprints posted under arXiv's non-exclusive license.
