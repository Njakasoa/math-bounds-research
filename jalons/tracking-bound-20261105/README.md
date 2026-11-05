# Tracking a moving reciprocal target

Classical discrete tracking estimates, formalized in Lean 4.34.1, for the global scalar realization from the Bernstein milestone. The key additional assumption controls input variation. No novelty or sharpness claim is made.

Read RESULTAT_SUIVI_FR.md for the result and limitations. The finite forcing convolution retains each input increment. With per-step variation at most δ, the concrete bound is e(n) ≤ (12/13)^n e(0) + 26δ(1−(12/13)^n).

The proof package contains four unchanged Bernstein dependencies and three new modules. The earlier published stage remains separate. This is a mathematical artifact, not an application validation.
