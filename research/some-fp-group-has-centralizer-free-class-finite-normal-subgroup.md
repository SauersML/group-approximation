---
rg: 2
id: some-fp-group-has-centralizer-free-class-finite-normal-subgroup
kind: claim
title: Some infinite finitely presented group has a finitely generated normal subgroup with trivial centralizer, finitely many ambient conjugacy classes and an F_3 quotient
distinct_from:
  universal-fiber-product-data-for-word-problem-groups: that asks for the data for EVERY finitely generated group with solvable word problem, with the input embedded in T; this asks for the data to exist ONCE, for some infinite T, with no embedding condition. It is the existence gate that every instance of that claim at an infinite input must pass.
  every-wp-group-embeds-in-fp-conjugacy-finite-group: that is the universal N = T case with an embedding condition, and is refuted by element orders; this is a single existence statement with N allowed proper, and the element-order refutation does not touch it.
  some-infinite-fp-torsion-free-group-has-finitely-many-classes: that asks for a torsion-free T with finitely many classes of its own, the case N = T; this allows torsion and a proper N whose classes are counted in T, and it is implied by that claim (a torsion-free group with finitely many classes is centreless), not equivalent to it.
  decidable-groups-embed-in-orbit-finite-affine-actors: that asks for orbit-finite affine actions S x| W for every decidable input; this asks only for one normal subgroup with finitely many ambient classes, and trivial centralizer is required here, which fails for an abelian S.
---

**OPEN.**

## Statement

There are a finitely presented infinite group `T` and a normal subgroup
`N <| T` such that `N` is finitely generated, `T/N` is of type `F_3`,
`C_T(N) = 1`, and `N` has only finitely many `T`-conjugacy classes.

## Where it sits

- **The data at any infinite input implies it.** If `(T, N)` is fiber-product
  data for an infinite `G` (`universal-fiber-product-data-for-word-problem-groups`),
  then `T >= G` is infinite, and the four conditions above are clauses 2--6. So
  a disproof of this claim refutes the universal claim at every infinite input,
  in particular at `G = Z`, and the universal claim can only be true if this
  one is.
- **The torsion-free `N = T` problem implies it.** If `T` is infinite, finitely
  presented and torsion-free with finitely many conjugacy classes
  (`some-infinite-fp-torsion-free-group-has-finitely-many-classes`), take
  `N = T`. Then `N` is finitely generated, `T/N = 1` is of type `F_infinity`,
  and `Z(T) = 1`: a central `z != 1` has infinite order, and the powers `z^m`
  are pairwise distinct central elements, each its own class. So a disproof
  of this claim also refutes that one.
- **Neither implication reverses in any evident way.** Here `N` may be proper
  and have infinitely many classes of its own, and torsion is allowed.

So this is the common existence gate of the two open construction problems in
the conjugacy-finite lane.

## Constraints on any witness (drafted elsewhere, pending referee)

By `class-finite-normal-subgroups-are-invisible-to-standard-hosts`, any witness
has:

- `N` infinite (a finite `N` with `C_T(N) = 1` gives `T <= Aut(N)` finite);
- `T` not residually finite, and `[N : R(N)] < infinity`, so a finite-index
  subgroup of `N` lies in every finite-index subgroup of `N`;
- every element of `N` torsion or distorted in `T`, with zero stable length in
  every isometric action of `T` and vanishing under every homogeneous
  quasimorphism of `T`;
- `N` in the kernel of every action of `T` that satisfies (CP), such as a
  Cantor action containing standard `V`, and of every action on `(0,1)` whose
  image contains standard `F`.

Further elementary constraints:

- **`[T : N]` is infinite.** If it were finite, each `T`-class in `N` would be
  a union of at most `[T : N]` classes of `N`, so `N` would be an infinite
  finitely generated group with finitely many conjugacy classes and a finitely
  presented overgroup of finite index. Then `N` is finitely presented, which is
  the open `N = T` case with torsion allowed. So a genuinely new witness has
  infinite quotient `T/N`, and that quotient must be infinite of type `F_3`.
- **`T` embeds in `Aut(N)`** through conjugation, since `C_T(N) = 1`. So `N`
  is a finitely generated, centreless, infinite group with finitely many
  `Aut(N)`-orbits, and realizes finitely many element orders
  (`fiber-product-conjugation-action-lemma`). Osin's groups show that such `N`
  exist as abstract groups. What is open is a finitely presented subgroup of
  `Aut(N)` containing `Inn(N)`, still with finitely many orbits and an `F_3`
  quotient by `Inn(N)`.

## Attempts

1. **Take `N` Thompson's `T` inside its normalizer in `Homeo(S^1)`.** Dies
   twice at the class count: element orders in Thompson's `T` are unbounded,
   and the rotation number is invariant under orientation-preserving conjugation
   and changes only by sign under reversing conjugation. It takes infinitely
   many dyadic values on the rotations in `T`.
2. **`N = Z^n`, `T = Z^n x| GL_n(Z)`.** Dies at item 1 of the invisibility node
   (the host is residually finite), concretely through the invariant `gcd` of
   the coordinates. It also dies at clause 5, since `N` centralizes itself.
