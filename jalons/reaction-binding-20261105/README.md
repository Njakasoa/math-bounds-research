# A toy reaction-network benchmark for certified tracking

Classical reversible single-site binding with an externally prescribed ligand. The package separates the normalized continuous equation, its forward-Euler discretization, contraction, physical interval preservation, and discrete target tracking.

Key falsifiable benchmark: the signed contraction checker accepts an Euler step whose next free-receptor fraction is −1/5. A model-specific rational physical guard rejects it. A smaller admissible step preserves [0,1] and has a proven input-variation tracking bound.

Read RESULTAT_REACTION_FR.md for assumptions and limitations, SOURCES_FR.md for prior literature and the actual level of source access, and README_REPRODUCTION_FR.md to rebuild. No empirical data, biological validation, general reaction-network theorem, numerical accuracy certificate, or novelty claim is provided.
