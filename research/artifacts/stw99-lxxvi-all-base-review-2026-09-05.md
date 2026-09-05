# Review and validation of the all-base Cu results

The following three proofs were reviewed together on 5 September 2026:

- [Soft first-factor isomorphism](stw99-lxxvi-soft-realification-surjectivity-audit-2026-09-05.md).
  The canonical APT realification and W-tensor isomorphisms track the
  actual map, so the argument proves surjectivity as well as order
  reflection. Proposition 7.5.12 applies to arbitrary C*-algebras;
  Corollary 7.5.10 identifies realification with the soft part for a
  pure Cu-semigroup. These hypotheses were checked in the primary text.
- [All-base projection rigidity](stw99-lxxvi-all-base-compact-k-stability-audit-2026-09-05.md).
  The proof classifies actual projection bundles with a fixed fiber,
  handles component conjugation in sphere clutching, and uses the
  specified corner map. Its extension to compact metrizable bases uses
  continuity of V, rather than a finite-dimensional assertion about
  every such base. Its general equivalence and real-rank-zero corollary
  concern projection classes; arbitrary positive classes are not
  inferred from them.
- [Full residual projectionless theorem](stw99-lxxvi-residually-stably-projectionless-audit-2026-09-05.md).
  Every quotient is explicitly controlled on both sides. The
  Gupta--Jain tensor-ideal theorem was checked with the simple exact
  factor Z; no exactness of the other factor is assumed. Finite-stage
  projection perturbation and point evaluation show that Z creates no
  projection over a stably projectionless algebra. The spectral
  softness criterion then makes the soft theorem apply to the entire
  source and target semigroups.

No unresolved gap was found in these arguments. They use published
structural theorems and do not claim external peer review or formal
verification. The full STW LXXVI problem remains open in this graph.
The moving-positive mixed-gluing argument is not part of this review.

## Source and graph checks

A fresh snapshot of all flat research Markdown files passed the native
Cairn document parser, reference and artifact lint, graph solver, and
unfiltered duplicate scan: **14,104 nodes, zero findings, zero duplicate
candidates**, in 9.219 seconds on MSI. Artifact existence was checked
against the contemporaneous local file inventory; historical pins were
checked using the remote Git object database. This validates the whole
source snapshot, not the mathematical contents of every other lane.

The archive SHA-256 is
`77da435183ca62694f9f3f47c5f4a4e7721900fa99698f86dfe76497e4b8a9da`.
The detailed remote record is
`stw79-cairn-check-20260904/cu-full-source-audit-20260905.json` under
`/projects/standard/hsiehph/sauer354`; it includes per-source hashes.
This clean snapshot supersedes the earlier 37-error snapshot report.

The original dependency closure also passed the actual CLI commands
`cairn check --changed` and `cairn preview`: 20 claims and 20 routes.
The temporary check directory initially lacked the GroupApproximation
artifact link used by an existing prerequisite. Linking the existing
artifact directory repaired that check environment; no proof source
was weakened or stubbed. The successful logs are in
`stw79-cairn-check-20260904/cu-all-base-scope-20260905`.

The three new claims derive `ESTABLISHED`, the LXXVI root remains
`OPEN`, and the previously reviewed LIX universal assertion remains
`REFUTED`. Those are graph derivations from the written routes, not
independent proof-kernel certifications.
