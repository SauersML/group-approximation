---
rg: 2
id: even-fc-artin-groups-satisfy-permutational-boone-higman
kind: claim
title: Every even Artin group of FC type, and every even Artin group whose cliques have irreducible factors of type Z, I_2(2k) or C̃_2, embeds in a finitely presented simple group
distinct_from:
  artin-groups-satisfy-boone-higman: that is the open problem over all Artin groups; this settles the even graphs whose cliques factor into vertices, edges and 4-4 paths, a class containing every even FC-type Artin group.
  spherical-artin-groups-satisfy-permutational-boone-higman: that is the spherical types, through linearity; this is an infinite family of non-spherical, non-Euclidean even Artin groups glued from spherical and C̃_2 cliques, for which no linearity is recorded.
  c-tilde-artin-groups-satisfy-permutational-boone-higman: that is the single Euclidean family C̃_n, through braid groups; this uses C̃_2 only as a clique factor and glues it with others along twisted amalgams.
  admissibly-oriented-artin-groups-satisfy-boone-higman: that is an open 2-dimensional class reduced to HNN permanence over free edge groups; this is a proved class of even graphs of any dimension, reached through retractions across even edges.
  artin-pbh-reduces-to-odd-component-cliques: that is the reduction to clique subgraphs; this is its unconditional consequence, where every clique factor is already known to lie in B_A.
artifacts:
  - research/artifacts/bh-common-retract-amalgams-even-artin-2026-09-16.md
---

Proved by the route `even-fc-artin-pbh-via-clique-reduction`. It has not been
independently reviewed. The novelty check is bounded; see §8 of the artifact.

## Statement

Let `Γ` be a finite graph whose labels are all even (non-edges are `∞`). For a clique
`Δ`, let `D(Δ)` be the subgraph of edges of `Δ` with label at least 4, on all the
vertices of `Δ`. Suppose that for every clique `Δ`, each connected component of
`D(Δ)` is one of:
- a single vertex;
- an edge;
- a path of two edges, both labelled 4.

Then `A_Γ` lies in `B_A`. So it embeds in a finitely presented simple group and has
solvable word problem.

**Even FC type.** For even `Γ`, being of FC type means that every triangle has at least
two labels 2. Then every `D(Δ)` is a matching, so the hypothesis holds. Hence **every
even Artin group of FC type embeds in a finitely presented simple group.**

## Examples

- **The labelled 4-cycle** `a -4- b -4- c -4- d -4- a`.
  - It is not virtually cocompactly cubulated, by Huang--Jankiewicz--Przytycki,
    arXiv:1510.08493v1, Theorem 1.1 (quoted in the artifact, §8).
  - Its splitting `A(b -4- a -4- d) *_(<b,d>) A(b -4- c -4- d)` is twisted, because
    `<b, d>` is not a direct factor of either side. So the untwisted retract amalgams
    of `pbh-class-closed-under-graph-products` do not reach it.
- **Every even Artin group with triangle-free defining graph.**
- **A non-FC example:** the `C̃_2` triangle `a -4- b -4- c`, `m_ac = 2`, with a pendant
  edge `c -6- d`.

## What is new

- As far as the bounded search found, this is the first Boone--Higman theorem for even
  Artin groups beyond right-angled, spherical, Euclidean and forest-defined ones.
- The known structure theory of even FC-type Artin groups gives poly-freeness and
  residual finiteness (Blasco-García--Martínez-Pérez--Paris, arXiv:1705.05574v1). The
  arXiv title search `"even Artin"` of 2026-09-16 found no linearity or embedding
  results.
- If even FC-type Artin groups were known to be linear in characteristic zero, the FC
  part would follow from `char-zero-linear-groups-satisfy-permutational-boone-higman`.
  The non-FC part and the method would stay new. That search was bounded and did not
  cover MathSciNet.

## Scope

- Not covered: even graphs with a clique factor outside the three types. The first ones
  are the hyperbolic triangles `(2,4,6)`, `(2,6,6)`, `(4,4,4)` and `(4,4,6)`, and every
  larger irreducible even clique.
- By `artin-pbh-reduces-to-odd-component-cliques`, those irreducible even cliques are
  exactly what remains of the permutational form of Boone--Higman for even Artin
  groups.

## Attempts

1. **Linearity through virtual specialness.** *Stops.* Even FC-type Artin groups are not
   virtually cocompactly cubulated in general (the 4-cycle above), and the search found
   no linearity theorem.
2. **Untwisted graph-product closure.** *Stops.* The star splittings of even Artin groups
   are twisted amalgams over retracts, not of the form `X *_C (C × K)`.
3. **Common-retract amalgams across even edges.** *Works*, through
   `artin-pbh-reduces-to-odd-component-cliques`.
