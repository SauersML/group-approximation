---
rg: 2
id: fixed-actor-orbit-quotients-are-finitely-many-proof
kind: route
title: Invariant relations are unions of pair orbits, faithful orbit partitions are kernels of invariant quotients, and actors with finite data are countable
target: fixed-actor-orbit-quotients-are-finitely-many
requires: []
---

Notation is as in the claim. `P` acts on `X × X` diagonally. It has `m` orbits
there, and `k` orbits on `X`.

**(1) Invariant relations.** Let `E ⊆ X × X` be a `P`-invariant equivalence
relation. Invariance means `(x, y) ∈ E ⇒ (gx, gy) ∈ E`, so `E` is a union of pair
orbits. The diagonal `Δ_X` is `P`-invariant, and the orbit of `(x, x)` is
`{(gx, gx)}`. So `Δ_X` is the union of exactly `k` pair orbits, one for each orbit
on `X`. Every equivalence relation contains `Δ_X`. So `E` is determined by which
of the remaining `m - k` pair orbits it contains, which gives at most `2^(m-k)`
relations.

**(2) Faithful orbit partitions.** Let `N ⊴ P`, and let `E_N` be the relation
`y ∈ Nx`.
- It is an equivalence relation, because `N` is a subgroup.
- It is `P`-invariant: if `y = nx`, then `gy = (g n g^{-1}) gx` with
  `g n g^{-1} ∈ N`.

So `P` acts on `X/N := X/E_N`. Its kernel `K_{E_N}` is the set of elements
preserving every `N`-orbit. The faithful-orbit-partition hypothesis says exactly
`K_{E_N} = N`. Hence `N ↦ E_N` is injective on such subgroups, since
`N = K_{E_N}` is recovered from `E_N`. By (1) there are at most `2^(m-k)` of them.
Also `P/N = P/K_{E_N}` acts faithfully on `X/N`, so `(P/N, X/N)` is the
orbit-quotient actor of `E_N`.

**(3) Iteration.** Put `Q = P/K_E` and `Y = X/E`. Let `E'` be a `Q`-invariant
equivalence relation on `Y`, and define `x E'' y` iff `[x] E' [y]`.
- `E''` is an equivalence relation on `X`.
- `E''` is `P`-invariant, because `P` acts on `Y` through `Q`.
- The map `X/E'' → Y/E'` sending `[x]_{E''}` to `[[x]_E]_{E'}` is a
  well-defined `P`-equivariant bijection.

So `K_{E''}`, the elements of `P` fixing every `E''`-class, is the preimage in
`P` of `K_{E'} ≤ Q`. Hence `P/K_{E''} ≅ Q/K_{E'}`, compatibly with the bijection,
and `(Q/K_{E'}, Y/E')` is isomorphic to the orbit-quotient actor of `E''`. By
induction every finite iterate is an orbit-quotient actor of `(P, X)`, and (1)
bounds their number by `2^(m-k)`. Isomorphic actors give isomorphic twisted
Brin–Thompson groups, because `SV` is built from the action alone. So there are
at most `2^(m-k)` groups `SV_{P/N}`. Item 2 of the claim is the case `E' = E_{N'}`
of this argument.

**(4) Countability of `𝒞`.** Finite presentations form a countable set, so
there are countably many finitely presented `P` up to isomorphism.

Fix `P`. An action with finitely many orbits (implied by finitely many pair
orbits) is determined up to isomorphism by picking one point in each of the
`k` orbits. Then `X ≅ ⊔_{j ≤ k} P/B_j` as `P`-sets, where `B_j` are the point
stabilizers. When the `B_j` are finitely generated, each is named by a finite
subset of the countable set `P`. So there are countably many such `P`-sets for
each `P`.

Each has at most `2^(m-k)` invariant relations by (1), and the orbit-quotient
actor is determined up to isomorphism by `(P, X, E)`. A countable union of
finite sets is countable.

**(5) Stabilizer obstruction.** Let `G ↷ S` be faithful of type [HA_2]. Suppose
some finitely presented `H` and surjection `π: H → G` make every point
stabilizer of `H ↷ S` finitely generated. Then `H ↷ S` is of type [A_2]:
- `H` is finitely presented;
- point stabilizers are finitely generated;
- `H` and `G` have the same orbits on `S × S` because `π` is onto, so there are
  finitely many.

This is FFWZ Definition 1.3 with `n = 2`, as quoted in
`a2-kernel-removable-iff-image-in-type-a2-actor`: stabilizers of pairs must
have type `F_0`, which is no condition. Its kernel is `ker π`, because `G ↷ S`
is faithful. So `(G, S) ≅ (H/ker π, S)` is the orbit-quotient actor of the
trivial relation `Δ_S`, and `(G, S) ∈ 𝒞`.

The members of `𝒜` are pairwise non-isomorphic, so at most countably many of
them are isomorphic to members of `𝒞`, by (4). Every other member has the stated
property.

**Consequence.** `SV_G` depends only on the isomorphism type of `G ↷ S`. A route
whose uncountable parameter is a perfect normal subgroup or an invariant
quotient of one actor ranges over a finite set, by (2) and (3). A route over
type [A_2] kernels ranges over `𝒞`, which is countable by (4). A countable group
has countably many finitely generated subgroups, so each route gives countably
many isomorphism types of simple groups or their finitely generated subgroups.
