# Group Approximation

The remote `verified` branch is automatically fast-forwarded after every complete Lean Prover CI success on `main`. Use that for the most recent correct Lean code.

## A non-MF group
[`non_mf_groups_exist.tex`](non_mf_groups_exist.tex) proves that not every group is MF. [`non_mf_group_notes.tex`](non_mf_groups_exist.tex) gives further notes on this.

## Lean formalization
The Lean development proves that the explicit finitely presented group in the paper is sofic and hyperlinear but not MF. The submission-facing theorem is `ExplicitNonMF.explicit_fp_sofic_hyperlinear_not_MF` in [`PalomarSolution.lean`](PalomarSolution.lean), and [`GroupApproximation.lean`](GroupApproximation.lean) imports the full formal library. The torsion-free non-MF extension is still being formalized and is not yet part of the verified Lean claim.
