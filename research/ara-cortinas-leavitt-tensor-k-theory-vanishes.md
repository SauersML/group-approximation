---
rg: 2
id: ara-cortinas-leavitt-tensor-k-theory-vanishes
kind: claim
title: Tensoring with the binary Leavitt algebra kills the algebraic K-theory of regular supercoherent algebras, so L ⊗ L has trivial K-theory
distinct_from:
  leavitt-unit-group-finitely-presented: that is finite presentability of the unit group of L; this is vanishing of algebraic K-theory for L ⊗ R with R regular supercoherent, a ring invariant with no group presentation in it.
artifacts:
  - research/artifacts/boone-higman-leavitt-tensor-hosts-2026-09-12.md
---

**ESTABLISHED (literature import).** Over every field `k`:

1. the Leavitt path algebra `L_k(E)` of a finite graph `E` is regular
   supercoherent;
2. if `R` is a regular supercoherent `k`-algebra, then `K_i(L_2 ⊗_k R) = 0`
   for every `i ∈ Z`.

In particular `K_*(L ⊗ L) = 0` for `L = L_(F_2)(1,2)`.

**Source.** P. Ara and G. Cortiñas, *Tensor products of Leavitt path algebras*,
arXiv:1108.0352v3, Section 6. The statements below were read from the PDF text
on MSI on 2026-09-12.
- Lemma 6.1: "Let E be a finite graph. Then L(E) is regular supercoherent."
- Proposition 6.2: "Let R be regular supercoherent. Then the algebraic
  K-theories of L_2 and of L_2 ⊗ R are both trivial."
- The abstract: "K_*(L_2) = K_*(L_2 ⊗ L_2) = 0".

The proof of Proposition 6.2 writes `L_2 ⊗ R = L_R(E)` and applies
Ara--Brustenga--Cortiñas arXiv:0903.0056, Theorem 7.6.

**Scope.** Nothing here covers `L^(⊗d)` for `d >= 3`: the source does not show
that `L ⊗ L` is regular supercoherent. That case is the open claim
`leavitt-tensor-powers-have-trivial-k-theory`.
