# Euler error for the toy binding model

Classical local consistency and contractive global error estimates, formalized in Lean 4.34.1. Euler and the exact sampled trajectory use the same mesh-aligned piecewise constant input. With 0<τ≤1/(1+M), the same-initial-state error at grid points is bounded by τ(1+M)²/2, uniformly in the number of steps.

Read RESULTAT_ERREUR_FR.md for the finite bound, physical assumptions, and exclusions. Read SOURCES_FR.md for directly consulted classical references, and README_REPRODUCTION_FR.md for reconstruction.

No novelty, biological validation, arbitrary intra-step forcing guarantee, or floating-point accuracy guarantee is claimed. This extends the earlier toy binding benchmark without changing its sources.
