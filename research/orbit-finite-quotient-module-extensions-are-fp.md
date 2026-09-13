---
rg: 2
id: orbit-finite-quotient-module-extensions-are-fp
kind: claim
title: A quotient of a permutation module by a finitely generated submodule gives a finitely presented split extension when stabilizers are finitely generated and double cosets are finite
distinct_from:
  direct-sharp-actor-wreath-forces-actor-fp: that is a necessary condition (finite presentation of a lamp group forces finite presentation of the actor); this is a sufficient condition for finite presentation of a split extension by a quotient module.
  orbit-finite-affine-actions-are-type-a: that turns a finitely presented orbit-finite extension into a type (A) actor; this supplies finite presentation of the extension from permutational data.
---

**ESTABLISHED** by `orbit-finite-quotient-module-extension-fp-proof`. Elementary;
no novelty is claimed. With `K = 0` and one orbit it is the sufficiency direction of
the classical finite presentation criterion for permutational wreath products
(not re-read here).

## Statement

Let `p` be a prime and `W` a finitely presented group. Let `H_1, ..., H_k <= W` be
finitely generated subgroups, `M = ⊕_i F_p[W/H_i]` the permutation module with basis
`e_(i, gH_i)`, and `K <= M` an `F_p W`-submodule that is finitely generated as a
module. Put `V = M/K`. If every double coset space `H_i \ W / H_j` is finite, then
`V ⋊ W` is finitely presented.

## Consequence recorded with the proof

Under these hypotheses let `O ⊂ V` be the union of the orbits `W·v_i` of the images
`v_i` of `e_(i, H_i)`. If `W` acts faithfully on `V`, then `W` acts faithfully on `O`
(the orbits span `V`), point stabilizers are conjugates of the `H_i`, and the
orbits on `O × O` correspond to the finitely many double cosets. So `W` acting on `O`
is already of type (A) in BFFHZ's sense. Any affine actor produced through this
criterion therefore contains its acting group inside a type (A) actor already.
