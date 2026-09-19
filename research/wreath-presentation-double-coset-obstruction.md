---
rg: 2
id: wreath-presentation-double-coset-obstruction
kind: route
title: A graph product absorbs any finite relator set, and height gives infinitely many double cosets
target: compression-wreath-not-finitely-presented
requires: []
artifacts:
  - research/artifacts/multi-mover-hnn-dossier-2026-08-15.md
---

## Why sufficient

Two halves.

**Infinitely many diagonal orbits.**  For a transitive action on `G*/Gamma*`,
diagonal orbits on the square are classified by double cosets: translate the
first coordinate to the base point and the residual stabilizer `Gamma*` acts
on the second.  The height homomorphism `chi` is zero on `Gamma*` and sends
`t` to `1`, so every element of `Gamma* t^n Gamma*` has height `n` and the
double cosets `Gamma* t^n Gamma*` are pairwise distinct.

**Finite presentation forces finitely many.**  Suppose `W = K^(X) x| G` is
finitely presented, with `X = G/Gamma` transitive and `Gamma` finitely
generated.  Killing the finitely many generators of the root lamp copy kills
the whole lamp base (transitivity), so `G` is finitely presented too.  The
free permutational precursor `E = (free product over X of K_x) x| G` is then
finitely presented on the same generating set, by the presentation whose only
extra relations say that the root copy of `K` is centralized by its
stabilizer.  Comparing finite presentations of `E` and `W` on that common
generating set makes the kernel `C` of `E ->> W` finitely *normally*
generated, so finitely many cross-site commutators `[k_x, l_y]`, meeting only
finitely many `G`-orbits of pairs, suffice to generate it normally.

Let `Graph` be the `G`-invariant graph on `X` whose edges are exactly those
finitely many orbits, and `E_Graph` the corresponding graph product semidirect
`G`.  Every relator used to express the normal generators dies in `E_Graph`,
so `C` dies, so `W` is a quotient of `E_Graph`; imposing the remaining
commutators gives the converse surjection, and both are the identity on
generators, so `W = E_Graph`.  If some orbit of distinct pairs is missing from
`Graph`, pick a non-edge `x != y` and retract the graph-product base onto the
free product `K_x * K_y`, where the reduced word `k_x l_y k_x^-1 l_y^-1` is
nontrivial — contradicting commutativity of distinct-site lamps in `W`.

**Finite-index and commensurability.**  Finite presentability passes down to
finite-index subgroups by Reidemeister--Schreier and up to finite-index
overgroups by adjoining finitely many coset-multiplication and conjugation
relations to a presentation of the normal core.  So no finite-index subgroup
is finitely presented and no finitely presented group is commensurable with
`W_K`.

Generator count: `G*` needs the six affine generators plus the stable letter,
and transitivity spreads one root copy of `K` over all sites.

## Ancestry

This is the necessity direction of Cornulier's finite-presentation criterion
for permutational wreath products (arXiv:math/0509090), specialized to the
transitive case and reproved here so that the graph does not depend on an
unread statement.  The result should be attributed there, not claimed as new;
what is specific to this family is the height computation that supplies the
infinitely many double cosets.

## Consequence for the programme

The finitely presented sofic non-MF endpoint cannot be reached inside this
wreath family.  It is already held by the presented group `E`
(`finitely-presented-sofic-non-mf`), by a different construction; any attempt
to re-derive it from a compression wreath product is dead space.
