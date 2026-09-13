---
rg: 2
id: type-semigroup-reflects-paradox-of-steinberg-algebra
kind: claim
title: Open - if the unit of a Steinberg algebra is paradoxical in its Murray-von Neumann monoid, is the unit space class paradoxical in the type semigroup
distinct_from:
  simple-ring-stably-finite-iff-unit-not-paradoxical: that is the ring-level equivalence between stable finiteness and paradox of [R] inside V(R); this asks whether that ring-level paradox descends to the type semigroup of the groupoid, which is what would make the property field-independent.
  algebraic-tarski-for-steinberg-algebras: that proves the transfer from groupoid paradox to ring paradox; this is the converse direction.
artifacts:
  - research/artifacts/un-algebraic-tarski-2026-09-13.md
---

**OPEN.** Let `𝒢` be a minimal, effective, Hausdorff, ample, second countable groupoid with compact
unit space `X`, `k` a countable field, `R = A_k(𝒢)`, and let
`ι : S(𝒢) → V(R)`, `[U] ↦ [1_U R]`, be the order-preserving monoid homomorphism of
`algebraic-tarski-for-steinberg-algebras-proof`. If `[1]` is paradoxical in `V(R)`, is `θ = [X]`
paradoxical in `S(𝒢)`? Equivalently, does `ι` reflect the paradox relation at `θ`?

**Why it matters.** `S(𝒢)` does not mention `k`. A positive answer would combine with
`simple-ring-stably-finite-iff-unit-not-paradoxical` to make stable finiteness of `A_k(𝒢)`
**independent of the field**: one dynamical property of `𝒢` would decide it simultaneously in
characteristic zero and characteristic `p`. It would also complete the groupoid-level identification
that `algebraic-tarski-for-steinberg-algebras` leaves one-directional.

## Attempts

- **Via an order-isomorphism `S(𝒢) ≅ V(R)`.** This would give the claim immediately and holds in both
  calibrating cases: `V(L_K(E)) ≅ M_E ≅ S(𝒢_E)` for graph groupoids (Ara–Moreno–Pardo), and for
  Cantor `Z`-systems. A bounded search by lane `un-prior-art` found no statement of it for general
  ample Hausdorff `𝒢`.
- **Where that dies.** `V(R)` is computed from arbitrary idempotents in `M_n(R)`, while the image of
  `ι` consists of the classes of compact open subsets of `X × ℕ`. Nothing here diagonalizes a general
  idempotent onto such a set, so surjectivity of `ι` is the missing step, and injectivity is a
  separate question.
- **Consistency check.** No counterexample is known either. Note the claim cannot be cheap: combined
  with `invariant-measure-gives-rank-function-in-char-zero` and the characteristic-zero equivalence, a
  positive answer would transport stable finiteness from characteristic zero to characteristic `p`
  for this class, which by `measure-side-stable-finiteness-contains-char-p-kaplansky` carries
  Kaplansky stable finiteness in characteristic `p`. So expect it to be at least Kaplansky-hard, and
  treat any short proof with suspicion.
- **A weaker target that would still help.** Surjectivity of `ι` up to stable equivalence, or
  reflection of paradox only at `θ` rather than at every element, would already suffice for the
  dichotomy.
