# SLAC/ABTS: ingestion audit and conditional model replay

This is a computational/descriptive assessment, not biological validation, a new parameter fit, or a new Lean theorem package. It uses the actual exported Michaelis–Menten/inactivation model, not the earlier single-site binding model.

Read ASSESSMENT_SLAC_FR.md first. The raw archive has sign/unit/initialization conventions that do not support silent generic-SBML interpretation. The explicit notebook-declared concentration ODEs can reproduce the saved model curves. Residual/stdev semantics remain unresolved, and concentration errors are reported descriptively, not as statistical coverage.

Inputs are external and opened read-only; see INPUTS.md for URLs and exact hashes. No download, installation, source-notebook execution, or external change is performed by these scripts.

With the pinned NumPy/SciPy versions in requirements.txt already available:

python experiments/audit_data.py /path/to/slac25.omex
python experiments/replay_declared_model.py /path/to/slac25.omex

The second command uses the supplied numerical curves extracted from the original saved notebook output. To independently repeat that extraction, provide the matching notebook JSON without executing it:

python experiments/extract_model_audit.py /path/to/slac25.omex /path/to/slac_kinetics.readonly.ipynb

The scripts regenerate results beside themselves. The main numerical replay was independently reproduced. Portable copies change only input-path/provenance plumbing, not equations or computations; replay output was checked byte-identical locally. Floating-point results may vary slightly across platforms, so numerical assertions use explicit tolerances. Check the distributed artifact with sha256sum -c SHA256SUMS before rerunning.

Expected scope: 264 concentrations, 800 saved prediction points; conditional ODE replay; exact-rational truncation-budget constants with a floating scalar Euler comparison. Neither floating/exp rounding nor experimental uncertainty coverage is certified. The scalar Euler test prescribes E(t) analytically; it is not simultaneous Euler on (S,E). A contraction claim on the full physical box must abstain because the transition fixes every (S,0).
