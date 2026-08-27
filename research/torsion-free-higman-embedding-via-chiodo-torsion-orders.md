---
rg: 2
id: torsion-free-higman-embedding-via-chiodo-torsion-orders
kind: route
title: Chiodo Theorem 2.2 - Higman embedding preserves the set of torsion orders
target: torsion-free-higman-embedding
requires: []
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
---

Literature import, and it closes this hole outright.  Direct reading of
arXiv:1107.1489v4 (Maurice Chiodo, *On torsion in finitely presented
groups*), page 3, on 2026-08-17.

**Definition 2.1.** `Tord(G) = { n in N : some g in G has order n >= 2 }`,
the set of orders of nontrivial torsion elements.

**Theorem 2.2**, quoted: *"There is a uniform algorithm that, on input of a
countably generated recursive presentation `P = <X|R>`, constructs a finite
presentation `T(P)` such that `P- ↪ T(P)` and `Tord(P-) = Tord(T(P))`, along
with an explicit embedding `phi- : P- ↪ T(P)`."*

## Why sufficient

Let `K` be recursively presented and torsion-free, presented by `P`.  Then
`Tord(K)` is empty, so `Tord(T(P))` is empty, so the finitely presented group
`T(P)` is torsion-free, and `K` embeds in it.  That is the claim, with a
uniform algorithm and an explicit embedding thrown in.

## Provenance and what it supersedes

Chiodo attributes Theorem 2.2 to [4, Lemma 6.9 and Theorem 6.10] and states
it is implicit in Rotman's proof ([13] Theorem 12.18) of the Higman embedding
theorem -- consistent with the informal argument the claim node used to
carry, that torsion in an HNN extension is conjugate into the base and
torsion in an amalgam into a factor.

This supersedes the node's previous "literature-plausible, not verified at
theorem level" status, and it removes the dependence on Belegradek that the
node correctly refused to rely on unread: the claim now rests on Chiodo
Theorem 2.2 alone, read and quoted above.  Chiodo--Hill (arXiv:1610.00977) is
a different and weaker statement -- finitely presented to finitely presented,
with 8 generators and 26 relators -- and is not needed.

Two neighbouring results from the same paper, both read, neither required
here: **Theorem 3.9**, a single finitely presented torsion-free group
containing every countably generated recursively presentable torsion-free
group; and **Theorem 3.10**, the universal finitely presented torsion-free
group, which Chiodo credits to Belegradek's appendix to [1] (Theorem A.1).
Theorem 3.9 is strictly stronger than what this repository's
`UniversalFinitelyPresentedTorsionFreeGroup` payload formalizes.

Trust surface: a `requires: []` literature import of one theorem, quoted
verbatim, whose specialization to the empty torsion-order set is the only
inference made.
