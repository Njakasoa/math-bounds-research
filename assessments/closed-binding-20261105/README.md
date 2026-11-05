# Choosing the open or closed single-site binding model

A decision assessment, not a new Lean proof milestone. It separates physical boundary conditions, observation horizon, absolute versus relative error, and parameter inference. Classical literature already covers ligand depletion and pseudo-first-order comparisons; no novelty or biological validation is claimed.

Read ASSESSMENT_FR.md for assumptions, analytical estimates, contrasting examples and the recommendation against further heavy formalization without a concrete observable, tolerance and horizon. SOURCES_FR.md records actual source access. REVUE_INDEPENDANTE_FR.md records the independent assessment.

Reproduce the 48 exact-rational equilibrium/capacity cases with:

python experiments/check_closed_binding.py

Only the Python standard library is required. The script regenerates experiments/closed-binding-results.json. Its equilibrium enclosures rely on the reviewed continuity/monotonicity argument; they are not Lean certificates. The transient error bound is an analytical derivation, not a numerical integration test. No experimental dataset or parameter fitting is included.

Check distributed files with sha256sum -c SHA256SUMS. This assessment does not modify the earlier published Lean milestones.
