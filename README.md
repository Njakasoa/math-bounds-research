# Certified polynomial atlas research

Independent mathematical research: finite rational atlas certificates and Lean proofs.

## Start here

- [Formal results and limitations (French)](RESULTAT_FORMEL_FR.md)
- [Reproduction instructions and pinned environment](README_REPRODUCTION_FR.md)
- [Independent review and its scope](REVUE_INDEPENDANTE_FR.md)
- `src/`: 25 proof modules, declaration audit and executable probes.
- `experiments/`: separate exact-rational Python experiments.
- `verification/`: recorded build, audit, review and experiment evidence.

The final proof snapshot was rebuilt with Lean 4.34.1 and the pinned Mathlib commit. The audit covers 104 declarations. The separate independent review covers 20 modules, not the TwoCell extension. No claim of mathematical novelty, extracted Lean synthesizer, global dynamical realization or switching stability is made. This archive does not recover the missing latest semantic-corona work.

## Reproduce

Follow README_REPRODUCTION_FR.md. The rebuild requires a prepared, pinned Lean/Mathlib environment; it does not install or download dependencies. Python experiments used Python 3.12.14 and SymPy 1.14.0; `requirements-experiments.txt` pins the direct and transitive packages.

## Publication hygiene

Only text sources and compact verification evidence are stored. Toolchains, caches, compiled objects, archives and personal notes are excluded. Two machine-specific import-path logs were omitted from the verified research snapshot for publication. No proof source was altered. SHA256SUMS covers this publication snapshot (excluding itself).
