---
rg: 2
id: orbit-finite-quotient-module-extensions-are-fp
kind: claim
title: A quotient of a permutation module by a finitely generated submodule gives a finitely presented split extension when stabilizers are finitely generated and double cosets are finite
distinct_from:
  direct-sharp-actor-wreath-forces-actor-fp: that is a necessary condition (finite presentation of a lamp group forces finite presentation of the actor); this is a sufficient condition for finite presentation of a split extension by a quotient module.
  orbit-finite-affine-actions-are-type-a: that turns a finitely presented orbit-finite extension into a type (A) actor; this supplies finite presentation of the extension from permutational data.
  augmentation-lamp-finite-presentation-criterion: that is finite presentation of the augmentation submodule extension over a 2-transitive actor, through Cornulier's theorem and index two; this is sufficiency for quotients of arbitrary permutation modules by finitely generated submodules, proved from an explicit presentation.
  bh-type-a-class-closed-under-permutational-lamp-wreaths: that puts finite lamps over a type (A) actor and obtains a type (A) action on S x B; this proves finite presentation of quotient-module extensions, and records that its hypotheses already make the actor of type (A) on the generating orbits.
---

**ESTABLISHED** by `orbit-finite-quotient-module-extension-fp-proof`. Elementary; no
novelty is claimed. With `K = 0` and one orbit it is the sufficiency half of Cornulier's
finite presentation theorem for permutational wreath products (quoted for lamp `C_2` on
`augmentation-lamp-finite-presentation-criterion`; not re-read here).

## Statement

Let `p` be a prime and `W` a finitely presented group. Let `H_1, ..., H_k <= W` be
finitely generated subgroups, `M = ⊕_i F_p[W/H_i]` the permutation module with basis
`e_(i, gH_i)`, and `K <= M` an `F_p W`-submodule that is finitely generated as a
module. Put `S = M/K`. If every double coset space `H_i \ W / H_j` is finite, then
`S ⋊ W` is finitely presented.

## Consequence recorded with the proof

Let `v_i ∈ S` be the image of `e_(i, H_i)` and `O = ∪_i W·v_i`. If `W` acts faithfully
on `S`, then `W` acting on `O` is of type (A) in BFFHZ's sense:
- it is faithful, since `O` spans `S`;
- the stabilizer `P_i` of `v_i` contains `H_i`, so it is a union of finitely many double
  cosets `H_i d H_i` and is finitely generated;
- orbits on `O × O` correspond to the double cosets `P_i \ W / P_j`, a quotient of the
  finite set `H_i \ W / H_j`.

So the hypotheses are the type (A) conditions for `W` acting on `⊔_i W/H_i` apart from
faithfulness, and this criterion yields affine actors only over acting groups that are
already type (A) actors.
