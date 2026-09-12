---
rg: 2
id: finite-normal-subgroups-do-not-affect-surjunctivity
kind: claim
title: For every finite normal subgroup, a group is surjunctive exactly when its quotient is
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
