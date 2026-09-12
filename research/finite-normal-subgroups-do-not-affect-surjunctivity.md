---
rg: 2
id: finite-normal-subgroups-do-not-affect-surjunctivity
kind: claim
title: For every finite normal subgroup, a group is surjunctive exactly when its quotient is
refuted_by:
  - deligne-triple-cover-nonsurjunctive
distinct_from:
  separated-finite-normal-subgroups-preserve-surjunctivity: that is the proved case where the finite normal subgroup injects into a finite quotient; this is the unrestricted statement, whose open residue is finite normal subgroups inside the finite residual.
artifacts:
  - research/artifacts/surjunctivity-closure-properties-2026-09-12.md
---

**OPEN.** If `N` is a finite normal subgroup of `E`, then `E` is surjunctive iff `E/N` is surjunctive.

**Status.**
- **Separated case.** Both directions are proved when `N` injects into a finite quotient of `E`
  (`separated-finite-normal-subgroups-preserve-surjunctivity`). This covers every virtually split finite
  central extension.
- **Open residue.** What remains is finite normal subgroups contained in the finite residual of `E`.
- **Test instance.** Deligne's triple cover of `Sp_4(Z)`: its finite residual is its center of order
  three (`deligne-triple-cover-finite-residual-is-center`). The quotient `Sp_4(Z)` is residually finite,
  hence surjunctive. No surjunctivity proof for the triple cover is recorded.
- **Relation to the conjecture.** The conjecture implies the claim. The claim does not give the
  conjecture, since infinite normal subgroups stay out of reach
  (`surjunctivity-passes-to-quotients`).

## Attempts

- **Table transfer through the quotient.** Reverse inequalities are never certified through a surjunctive
  quotient (corollary 2 of `strict-pairs-transfer-to-table-realizations`, and
  `surjunctivity-recognition-dichotomy`). Dually, a strict pair over `E/N` does not lift: lifting forward
  coincidences creates none, and the reverse witness may split into an `N`-coset. Neither direction moves
  a certificate.
- **Twisted shifts.** A set-theoretic section `E/N -> E` identifies `A^E` with `(A^N)^(E/N)`. The action
  becomes a shift over `E/N` twisted by an `N`-valued cocycle. Curtis–Hedlund–Lyndon converts only plain
  shifts, and the twist is plain over a finite-index subgroup exactly when the extension splits there,
  which is the separated case.
- **Linear central case.** For `p ∤ |N|`, `F_p[E]` splits along the characters of `N` into twisted group
  algebras `F_p^c[E/N]`. Stable finiteness of `F_p[E/N]` does not transfer to the twisted summands. The
  ternary split of the Leavitt unit group (`ternary-leavitt-swap-problem-splits-at-central-involution`)
  is an instance of this summand structure, where the anti-central summand is itself a counterexample
  target.
- **Linear, characteristics dividing the kernel: settled** (lane w3-deligne, artifact
  `deligne-triple-cover-surjunctivity-2026-09-12.md`). A finite normal `p`-subgroup never affects
  stable finiteness of characteristic-`p` group algebras, because its augmentation kernel is nilpotent
  (`finite-normal-p-subgroups-preserve-modular-stable-finiteness`). This holds inside the finite residual.
  So in characteristic `p` no strict linear automaton appears when `k[E/N]` is stably finite, and for
  central `N` the linear residue is exactly the nontrivial-character twisted algebras over `N_(p')`.
- **Memory filter** (lane w3-deligne). A strict automaton over `E` with `E/N` surjunctive has a memory
  group `H` with `N cap Res_fin(H) != 1`, and `H` is nonsofic
  (`strict-automata-memory-keeps-finite-normal-kernel-residual`).
- **The test instance now has its own nodes.** `deligne-triple-cover-surjunctive` is open, with the soficity
  route. `deligne-triple-cover-nonsurjunctive` is open, and would refute this claim.
  `k[E_3]` is stably finite in characteristic three
  (`deligne-triple-cover-ternary-group-algebras-are-stably-finite`). A second instance with a surjunctive
  nonsofic quotient is the Kun–Thom Clifford cover (`kun-thom-clifford-cover-nonsurjunctive`, lane
  w3-free-neg).
- **Clifford covers: one residue instance settled, in the predicted direction** (lane w4-clifford-nonlinear,
  artifact `clifford-cover-orbital-localization-2026-09-12.md`). Take a `G`-invariant graph `S` on
  `G/Gamma` and its cover `E_S`.
  - **Separated covers.** The center injects into a finite quotient exactly when `S` is pulled back from a
    finite quotient of the site set (`clifford-cover-center-separable-iff-graph-is-finite-pullback`).
  - **Beyond the separated case.** If `G` is surjunctive and `S` is profinitely saturated, `E_S` is surjunctive
    (`profinitely-saturated-clifford-covers-are-surjunctive`), by local embeddings into separated covers.
  - **An instance inside the residue.** Take the Kun--Thom pair and the cross graph, which joins sites
    lying in different fibres of `G/Gamma -> G/Gammabar`. Its center lies in the finite residual, and the
    cover is surjunctive.
  - **What local re-choice cannot reach.** The method re-chooses only the extension data read by finitely
    many products. The analogous cocycle re-choice for Deligne's triple cover is recorded on
    `deligne-triple-cover-nonsurjunctive`.
