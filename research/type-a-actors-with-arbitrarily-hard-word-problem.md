---
rg: 2
id: type-a-actors-with-arbitrarily-hard-word-problem
kind: claim
title: For every recursive time bound some finitely presented group with a faithful type (A) action has a harder word problem
distinct_from:
  permutational-boone-higman-conjecture: that asks for a type (A) actor containing EVERY decidable input; this asks only for one actor beyond each recursive bound, which that conjecture implies.
  fp-self-similar-groups-with-arbitrarily-hard-word-problem: that is the hard-input claim for the Rover--Nekrashevych branch of the complexity root; this is the hard-input claim for the twisted Brin--Thompson branch, and neither is known to imply the other.
  fp-simple-groups-with-arbitrarily-complex-word-problem: that is the root about finitely presented simple groups in general; this claim implies it and is equivalent to its restriction to finitely presented twisted Brin--Thompson groups.
---

**OPEN.** For every recursive `T: N -> N` there is a faithful action of type (A)
(`type-a-action-gives-boone-higman-for-subgroups`) of a finitely presented
group `G` whose word problem has no algorithm in time `C*T(C*l) + C*l + C` for
any constant `C`.

**Equivalent forms.** By (d) of `twisted-brin-thompson-wp-equals-actor-orbit-problem`
this is equivalent to:
- the same with "word problem" replaced by the orbit problem
  `OP(G,S)` (word problem plus point-stabilizer membership);
- for every recursive `T`, some finitely presented twisted Brin--Thompson group
  beats `T`;
- for every recursive `T`, some finitely presented simple MIF group (equivalently,
  highly transitive) beats `T`. This one uses BFFHZ Theorem C,
  `fp-simple-highly-transitive-groups-satisfy-pbh`.

So the root restricted to MIF witnesses *is* this claim. A positive answer to
BFFHZ Question 3.4 (`fp-simple-groups-embed-in-fp-simple-mif-groups`) would make
the whole root equivalent to it.

Its consequences:
- through `arbitrarily-complex-fp-simple-via-hard-type-a-actors` it implies the
  root `fp-simple-groups-with-arbitrarily-complex-word-problem`;
- by (c) there, it is also *necessary* for the twisted Brin--Thompson branch of
  that root, since a bounded family of actors gives a bounded family of hosts.

## Attempts

1. **From the permutational conjecture.** Route
   `hard-type-a-actors-from-permutational-boone-higman` derives this claim from
   `permutational-boone-higman-conjecture`. The input is the hard two-generated
   graph-shift groups. The route is open because the conjecture is open, and it
   asks for far more than one hard actor per bound.
2. **Iterate the clopen action.** Starting from any actor, take `SV_G`, act on
   clopen sets, and repeat. *Dies as a method.* By the iteration clause of
   `twisted-brin-thompson-wp-equals-actor-orbit-problem`, each round adds at most
   one exponential. Finite towers over a bounded actor stay elementary, and an
   infinite tower is not finitely presented.
3. **Actors of rational homeomorphisms.** A finitely presented full Cantor group
   containing V has a type (A) clopen action
   (`fp-full-binary-cantor-groups-have-type-a-actions`). Rational ones share the
   exponential bound of `rational-homeomorphism-subgroups-have-exponential-wp`.
   *Dies as a family*, by `complexity-bounded-host-classes-are-not-universal`.
   A hard example must be non-rational.
4. **Easy word problem, hard stabilizers.** By (a) of the orbit-problem theorem a
   hard stabilizer-membership problem suffices, even over an easy word problem.
   - *Why it looks promising.* A Mihailova subgroup of `F_2 x F_2 <= 2V` has
     membership problem equivalent to the word problem of any chosen finitely
     presented group.
   - *Where it dies.* A point stabilizer of a type (A) action has finitely many
     double cosets. Take the natural actor, `F_2 x F_2` on the cosets of the
     Mihailova subgroup of a finitely presented `Q`. Its faithful image is
     `Q x Q` acting on `Q` by `(x,y).q = x q y^-1`, and two-element subsets
     `{q, q'}` are classified by the conjugacy class of `q^-1 q'` up to
     inversion. So `Q` would need finitely many conjugacy classes, which is the
     open special case of `universal-fiber-product-data-for-word-problem-groups`.
     Inside a larger actor such as `2V`, the Mihailova subgroup is not a point
     stabilizer, and no enlargement to one is known.
   - *Status.* No actor of this kind is known.
