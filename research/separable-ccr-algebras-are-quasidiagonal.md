---
rg: 2
id: separable-ccr-algebras-are-quasidiagonal
kind: claim
title: A separable C*-algebra faithfully represented by a countable direct sum of representations into compact operators is quasidiagonal, so separable CCR algebras are quasidiagonal
distinct_from:
  bk-t1-primitive-spectrum-case: that is Problem VII for nuclear stably finite algebras with T_1 spectrum, open because of the simple case; this is the elementary CCR case, needing no nuclearity or finiteness hypothesis, and it settles only the type I part of that claim.
  bk-primitive-quotients-qd-or-traceless-force-qd: that is a fibrewise theorem for nuclear stably finite algebras built on Gabe's traceless theorem; this is a direct quasidiagonality argument when every irreducible image lies in the compacts.
  stw07-separating-qd-quotients-force-quasidiagonality: that assumes a separating family of quasidiagonal quotients; this assumes a separating family of representations landing in the compacts and builds the projections directly.
artifacts:
  - research/artifacts/bk-type-i-k0-embedding-equivalence-2026-09-16.md
---

**ESTABLISHED (Lemma 1 of the artifact, §1; elementary, presumably folklore,
no source checked).**

Let `A` be separable.  Suppose there are representations `π_i : A → B(H_i)`,
`i ∈ N`, on separable Hilbert spaces, with `π_i(A) ⊆ K(H_i)` and `⊕_i π_i`
faithful.  Then `⊕_i π_i(A)` is a quasidiagonal set of operators, so `A` is
quasidiagonal and hence stably finite.

In particular:

1. Every separable CCR (liminal) algebra is quasidiagonal.  A countable
   norming family of irreducible representations exists by separability, and
   CCR means each image lies in the compacts.
2. Every separable type I algebra with `T_1` primitive ideal space is
   quasidiagonal, being CCR.

The hypothesis `π_i(A) ⊆ K(H_i)` cannot be weakened to `π_i(A) ⊇ K(H_i)`: the
Toeplitz algebra is irreducible, contains `K` and is not quasidiagonal.  By
`toeplitz-pair-algebra-is-qd-with-non-qd-irreps` this matters even inside
quasidiagonal type I algebras.
