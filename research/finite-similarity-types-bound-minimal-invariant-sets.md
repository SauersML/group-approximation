---
rg: 2
id: finite-similarity-types-bound-minimal-invariant-sets
kind: claim
title: "An ample groupoid with m similarity types of basic clopen sets has at most m minimal closed invariant sets"
distinct_from:
  v-times-shift-alternating-group-restrictions-are-simple: That node counts the minimal invariant sets of G_V × (Z ⋉ Σ) (there are 2^aleph_0); this node proves a general upper bound on that count from finiteness of similarity types, and so rules out finite-type finiteness proofs for that groupoid.
---

**Setting.** `G` is an étale groupoid with totally disconnected unit space `X`.
A **similarity type system** of size `m` is a list of compact open sets
`B_1, ..., B_m ⊆ X` such that every point `y ∈ X` has a neighbourhood basis of
compact open sets `U` ("basic sets"). Each basic set is the range of a compact
open bisection `S_U` with source `s(S_U) = B_j` for some `j = j(U)`, its type.

**Theorem.** If `G` has a similarity type system of size `m`, then `G` has at
most `m` minimal nonempty closed `G`-invariant subsets.

Proof in `finite-similarity-types-bound-minimal-invariant-sets-proof`.

**Motivation** (not part of the statement). Brown-criterion proofs of finiteness
for full groups filter by the number of basic pieces. Examples are Stein–Farley
complexes of expansions, as in Matui's F_∞ proof for one-sided SFT groupoids, and
the complexes for groups of local similarities. For that filtration to be
cocompact, the one-piece vertices must fall into finitely many orbits. So the
basic pieces must come in finitely many similarity types, which is a similarity
type system in the sense above, with one `B_j` chosen per type. Consequence:
`v-times-shift-groupoid-has-no-finite-similarity-types`.
