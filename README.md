# Certified polynomial atlas research

Independent mathematical research: finite rational atlas certificates and Lean proofs.

## Start here

- [Formal results and limitations (French)](RESULTAT_FORMEL_FR.md)
- [Reproduction instructions and pinned environment](README_REPRODUCTION_FR.md)
- [Independent review and its scope](REVUE_INDEPENDANTE_FR.md)
- `src/`: 25 proof modules, declaration audit and executable probes.
- `experiments/`: separate exact-rational Python experiments.
- `verification/`: recorded build, audit, review and experiment evidence.

The initial atlas proof snapshot was rebuilt with Lean 4.34.1 and the pinned Mathlib commit. The audit covers 104 declarations. The separate independent review covers 20 modules, not the TwoCell extension. For this initial atlas snapshot, no claim of mathematical novelty, extracted Lean synthesizer, global dynamical realization or switching stability is made. This archive does not recover the missing latest semantic-corona work.

## Reproduce

Follow README_REPRODUCTION_FR.md. The rebuild requires a prepared, pinned Lean/Mathlib environment; it does not install or download dependencies. Python experiments used Python 3.12.14 and SymPy 1.14.0; `requirements-experiments.txt` pins the direct and transitive packages.

## Publication hygiene

Only text sources and compact verification evidence are stored. Toolchains, caches, compiled objects, archives and personal notes are excluded. Two machine-specific import-path logs were omitted from the verified research snapshot for publication. No proof source was altered. SHA256SUMS covers this publication snapshot (excluding itself).

## Subsequent verified milestone

[Bernstein global scalar realization, 2026-11-05](jalons/bernstein-global-20261105/README.md) adds seven Lean modules, a rational Bernstein checker and a single-state global example, with independent review, 63 declaration audits, seven executable probes and exact Python experiments. The original atlas sources remain unchanged.

For the Bernstein example the certified contraction factor is 12/13, optimal only for the fixed degree-5 coefficient envelope, not the true range (which allows 2/3). Synchronization under a shared input sequence does not imply tracking a moving instantaneous target. The bound checker requires a separate target-identity proof. No novelty claim is made.

See the milestone's [validation scope](jalons/bernstein-global-20261105/verification/BUILD_SCOPE.md): all individual build and check commands passed, but the final packaged driver was not rerun monolithically after a formatting-only script edit.

## Controlled-variation tracking milestone

[Tracking bounds, 2026-11-05](jalons/tracking-bound-20261105/README.md) adds three Lean modules proving a finite tracking-error bound for the same discrete scalar recurrence. If each input increment is at most δ, then e(n) ≤ (12/13)^n e(0) + 26δ(1−(12/13)^n), for any real initial state. Constants are conservative; bounded nonzero variation does not force the error to tend to zero.

The independent review ran the original rebuild script end-to-end in a fresh copy. All seven modules compiled; 21 named declaration audits plus the independently audited convolution_zero cover 22 new statements using only standard axioms. Four exact-rational Python experiments passed. This is a classical discrete estimate, with no novelty, continuous-time or synthesis claim. Earlier milestones remain unchanged.
