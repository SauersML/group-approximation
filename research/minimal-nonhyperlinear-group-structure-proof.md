---
rg: 2
id: minimal-nonhyperlinear-group-structure-proof
kind: route
title: Apply locality, amenable-quotient permanence and amenable-edge Bass--Serre permanence to the proper subgroups of a minimal nonhyperlinear group
target: minimal-nonhyperlinear-group-structure
requires:
  - local-approximation-properties-are-marked-closed
  - amenable-quotient-preserves-metric-approximability
  - amenable-edge-graph-corners-cannot-groupify-a-nonce-game
artifacts:
  - research/artifacts/lcs-five-equations-and-minimal-nonhyperlinear-2026-09-16.md
---

The full proof is Part II of the artifact, §II.2. Let `G` be MNH.

## Imports

- **(L)** `local-approximation-properties-are-marked-closed`, clauses 1--2:
  hyperlinearity is hereditary, and a group is hyperlinear iff all its finitely
  generated subgroups are.
- **(Q)** `amenable-quotient-preserves-metric-approximability`: if `N` is
  normal in `G`, `N` is hyperlinear and `G/N` is amenable, then `G` is
  hyperlinear. With `N = 1`, amenable groups are hyperlinear.
- **(AEG1)** `amenable-edge-graph-corners-cannot-groupify-a-nonce-game`: the
  fundamental group of a finite connected graph of countable groups with
  hyperlinear vertex groups and amenable edge groups is hyperlinear.

## (M1)

By (L), `G` has a finitely generated nonhyperlinear subgroup `K`. Minimality
forces `K = G`. By (Q) with `N = 1`, `G` is not amenable, and so it is
infinite.

## (M2)

A normal `N != G` is proper, hence hyperlinear. If `G/N` were amenable, (Q)
would make `G` hyperlinear.
- `[G,G]` has abelian quotient, so `[G,G] = G`.
- A proper finite-index subgroup has a normal core that is proper, normal and
  of finite index, which is excluded.

## (M3)

Let `phi : G -> R` be nontrivial with `R` residually finite, and pick `g` with
`phi(g) != 1`. A finite quotient `pi : R -> Q` with `pi(phi(g)) != 1` makes
`ker(pi o phi)` a proper normal subgroup of finite index, which contradicts
(M2).

## (M4)

`G` is countable by (M1). The canonical maps from vertex groups are injective
(Bass--Serre theory), so all vertex and edge groups are countable.
- If every vertex group were hyperlinear, (AEG1) would make `G` hyperlinear.
  So some `G_v` is nonhyperlinear.
- The image of `G_v` is isomorphic to `G_v`, so it is a nonhyperlinear
  subgroup. By minimality it is all of `G`.

## (M5)

Let `X` be a finite generating set.
- The union of a chain of proper normal subgroups is normal. It is proper,
  since otherwise the finite set `X` lies in one member.
- Zorn's lemma, starting from `1 != G`, gives a maximal normal `M`.
- `G/M` is simple and finitely generated. It is nonamenable by (M2), hence
  infinite.
- `M` is proper, hence hyperlinear.

## (M6)

Let `K` be nonhyperlinear with no MNH subgroup. By (L), pick a finitely
generated nonhyperlinear `G_0 <= K`. Given `G_i`, which is not MNH, pick a
proper nonhyperlinear subgroup `P < G_i`. By (L), pick a finitely generated
nonhyperlinear `G_(i+1) <= P`. Dependent choice gives the chain.
