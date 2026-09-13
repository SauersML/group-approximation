---
rg: 2
id: lodha-moore-commutator-simple-abelianization-z3
kind: claim
title: The Lodha--Moore group has a simple, compactly supported commutator subgroup, trivial centre, abelian proper quotients and abelianization Z^3 on the basis a, b, c
distinct_from:
  lodha-moore-group-is-bi-orderable-and-not-lea: that uses the abelian-quotient statement from the Burillo--Lodha--Reeves abstract to rule out LEA; this imports four structural facts from their text, including the abelianization basis and compact support, which the character classification of G_0 consumes.
---

**ESTABLISHED by citation.**  Let `G_0 = <a, b, c> = <x, x_1, y_10>` be the
Lodha--Moore group.

1. `G_0'` is simple.
2. Every proper quotient of `G_0` is abelian, and the centre of `G_0` is trivial.
3. The assignment `x -> (1,0,0)`, `x_1 -> (0,1,0)`, `y_10 -> (0,0,1)` extends to a
   surjective homomorphism `pi : G_0 -> Z^3` with kernel `G_0'`.
4. `G_0'` consists exactly of the compactly supported elements of `G_0` whose
   total exponent in the `y`-generators is zero.

Consumer: `lodha-moore-group-character-simplex`.

Derivation: `lodha-moore-commutator-simple-abelianization-z3-citation`.
