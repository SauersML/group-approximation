---
rg: 2
id: thompson-v-has-quadratic-dehn-function
kind: claim
title: Thompson's group V has quadratic Dehn function
distinct_from:
  thompson-t-has-quadratic-dehn-function: that is Migliorini's theorem for the group T; this is the open question for V.
---

**Open.** Conjecture (the V part of Zaremsky Problem 2.5): `δ_V(n) ≃ n^2`.

V contains F, and F contains `Z^2`, so V is not hyperbolic and `δ_V ≽ n^2`
(subquadratic Dehn function implies hyperbolic). The content is the upper bound.

## Attempts

- **Known upper bounds.** `n^11` (Guba 2000) and `n^6` (Lorrain, Theorem 5.7;
  `thompson-v-dehn-function-is-at-most-sextic`).
- **Where Lorrain's degree is lost (read from arXiv:2608.03813v2, pp. 60–65).**
  The area `A(n)` of rewriting a length-`n` word into Guba's normal form
  `p π c_(n+1)^m q^(-1)` satisfies `A(n) ≤ 2A(n/2) + M(n)`, where `M(n)` is the
  cost of merging two normal forms. The `O(n^6)` terms in `M(n)` come from
  π-words:
  - Lemma 4.8 makes a π-word irreducible with area `|π|_π^2 · O(n^2)`;
  - Corollary 4.6 bounds `|π|_π` by `O(n^2)`;
  - Lemma 4.14 moves a power of `c_(n+1)` across an irreducible π-word of rank
    `≤ n` with area `O(n^6)`.

  The `c`-letter relations cost `O(n^3)` (Lemma 2.4). With this recursion, a
  merge cost `M(n) = O(n^2)` would already give `A(n) = O(n^2)`, since
  `Σ_j 2^j (n/2^j)^2 ≤ 2n^2`. So quadratic follows from a quadratic merge.
- **Structural heuristic (not a theorem).** The π-letters `π_n` behave like
  adjacent transpositions of the infinite symmetric group, with Coxeter
  relations in the infinite presentation. An irreducible π-word of rank `n` can
  have π-length about `n^2/2`, the inversion number. By contrast, an element of
  V with `N` carets has word length only `O(N log N)`, per the introduction of
  Migliorini arXiv:2410.23088 (not yet checked against its source). So Guba's
  normal form can be quadratically longer than the word it represents, and a
  merge through it spends `Θ(n^2)` letters before any area is counted. A
  quadratic proof likely needs a compressed permutation normal form, such as
  sorting-network or merge-sort layers of subtree swaps, of length
  `O(n log n)`. It then needs a quadratic-area calculus for relations among
  those layers.
- **Migliorini's T method (per its introduction, as fetched; to be checked
  against the text).** Every element of T needs only a bounded number of non-F
  letters (one power of the rotation), and quadratic area reduces to triangular
  diagrams (Proposition 4.3) plus Guba's quadratic bound for F. In V the
  permutation part needs unboundedly many non-F letters, which is exactly the
  obstacle above.
- **Plan (lane z2-05-v-dehn, 2026-09-13).**
  1. Test whether every element of V with `N` carets factors as `f σ g` with
     `f, g ∈ F` and `σ` a product of `O(log N)` layers of disjoint subtree
     swaps. Each layer is an element of an abelian 2-group inside V.
  2. Bound the area of the relations among layers: commuting disjoint swaps,
     and conjugating a layer by F.
  3. Adapt Migliorini's triangular-diagram reduction to this factorization.
