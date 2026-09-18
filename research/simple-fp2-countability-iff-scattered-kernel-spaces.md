---
rg: 2
id: simple-fp2-countability-iff-scattered-kernel-spaces
kind: claim
title: "Simple FP_2 groups are countably many iff every finitely presented group has a scattered space of perfect maximal kernels; a counterexample carries a Cantor set of kernels with uniform moduli"
distinct_from:
  simple-fp2-uncountability-via-perfect-simple-quotients: that claim reduces the question to counting perfect kernels with simple quotient in one finitely presented group; this one puts the Chabauty topology on those kernels, proves the space is Polish, turns countability into scatteredness and Cantor-set freeness, and extracts the forced structure of a counterexample (perfect ambient, compact Cantor family, uniform moduli, multiplier surjection, non-computability)
  only-countably-many-simple-groups-of-type-fp2: that is the open target; this is an established equivalent reformulation plus forced structure, and leaves the target open
---

Let `H` be a finitely generated group with finite generating set `X`.

- `N(H) ⊆ {0,1}^H` is the space of normal subgroups of `H` with the
  product (Chabauty) topology. It is compact and metrizable.
- `MP(H) ⊆ N(H)` is the set of normal subgroups `N` that are **perfect** and
  **maximal**, meaning `N ≠ H` and `H/N` is simple.

**1. Topology.** `MP(H)` is a `G_δ` subset of `N(H)`, so it is a Polish space.

**2. Equivalences.** The following are equivalent.

- (a) Up to isomorphism there are at most countably many simple groups of
  type FP_2 (`only-countably-many-simple-groups-of-type-fp2`).
- (b) For every finitely presented `H`, `MP(H)` is countable.
- (c) For every finitely presented `H`, `MP(H)` is scattered: every nonempty
  closed subset has an isolated point.
- (d) For every finitely presented `H`, `MP(H)` contains no subspace
  homeomorphic to the Cantor set.
- (e) For every finitely presented `H`, only countably many maximal normal
  subgroups `N` have `H/N` of type FP_2.

**3. Kernel criterion.** For finitely presented `H` and `N ⊴ H`, the quotient
`H/N` is of type FP_2 iff `N = ⟨⟨F⟩⟩[N,N]` for some finite `F ⊆ N`.

**4. Biography of a counterexample.** Suppose (a) fails. Then there are a
finitely presented group `H` and a compact subset `K ⊆ MP(H)` homeomorphic to
the Cantor set with the following properties.

- (i) `H` is perfect.
- (ii) Every `H/N` with `N ∈ K` is an infinite simple group of type FP_2. The
  quotients `H/N` realize `2^aleph_0` isomorphism types.
- (iii) No `N ∈ K` is finitely normally generated, and no `N ∈ K` (as a set of
  words in `X`) is recursively enumerable or co-recursively enumerable.
- (iv) `H_2(H; Z)` maps onto `H_2(H/N; Z)` for every `N ∈ MP(H)`. So the Schur
  multipliers of all members are quotients of one finitely generated abelian
  group.
- (v) For pairwise distinct `N_1, ..., N_k ∈ K`, the map
  `H -> H/N_1 × ... × H/N_k` is onto.
- (vi) *Uniform moduli.* For each `w ∈ H` there is a finite set `E⁺(w)` of
  commutator expressions `w = [a_1,b_1]...[a_m,b_m]` such that every `N ∈ K`
  containing `w` has all the `a_j, b_j` of some expression in `E⁺(w)` inside
  `N`. For each `w ∈ H` and `x ∈ X` there is a finite set `E⁻(w,x)` of
  expressions `x = ∏_j g_j u_j g_j^{-1}` with each `u_j ∈ {w, w^{-1}}` or
  designated as an `N`-letter, such that every `N ∈ K` not containing `w` has
  all the designated `u_j` of some expression in `E⁻(w,x)` inside `N`.

Consequences:

- Every countability proof has to rule out a *compact, uniformly controlled*
  Cantor family inside one perfect finitely presented group. Arguments that
  only show an individual kernel is isolated in `MP(H)` prove nothing: the
  isolated points of any second countable space form a countable set.
- The target is exactly the scatteredness of the Polish spaces `MP(H)`.

Proof in `simple-fp2-countability-iff-scattered-kernel-spaces-proof`.
