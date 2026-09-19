---
rg: 2
id: twisted-integral-affine-groups-lie-in-the-permutational-class
kind: claim
title: Each twisted S-integral affine group W_(P,ℓ), including W, acts with type (A) on ordered partitions of Z_ℓ^D into ℓ clopen pieces of unit class, so it and all its subgroups lie in B_A
distinct_from:
  fp-clopen-transitive-full-cantor-groups-have-type-a-actions: that needs any two nonempty clopen sets to be joined by local maps, which fails for W_(P,ℓ) at odd ℓ because clopen sets carry a class in Z/(ℓ−1); this replaces clopen sets by ordered partitions into pieces of the class of the whole space, and covers W = W_(∅,2) as the case ℓ = 2 of that criterion.
  twisted-s-integral-affine-groups-are-fp-and-virtually-simple: that proves W_(P,ℓ) finitely presented and D(W_(P,ℓ)) simple; this puts W_(P,ℓ) and every subgroup of it into the permutational class B_A.
  one-fp-simple-group-contains-every-s-integral-linear-group: that gives one finitely presented simple host for all GL_n(Z[1/P]); this makes that host a B_A group, so it also has (SQ) and (JE) with every B_A group.
---

**ESTABLISHED** (lane proof, bh-major-product, 2026-09-18; elementary given the finite
presentation of `W_(P,ℓ)`, which is itself a lane proof awaiting referees; not independently
reviewed; no priority claimed).

## Statement

Let `P` be a finite set of primes, `ℓ ∉ P` a prime, `X = Z_ℓ^D`, and `W_(P,ℓ)` the group of
`twisted-s-integral-affine-groups-are-fp-and-virtually-simple`. `W = W_(∅,2)` is the group of
`twisted-integral-affine-full-group-is-finitely-presented`.

Let `μ` be Haar probability measure on `X`. The **class** of a clopen `U` is the image of
`μ(U) ∈ Z[1/ℓ]` in `Z[1/ℓ]/(ℓ−1)Z[1/ℓ] ≅ Z/(ℓ−1)`. Let `Ω_ℓ` be the set of ordered partitions
`(U_1, …, U_ℓ)` of `X` into nonempty clopen sets of class 1.

1. The action of `W_(P,ℓ)` on `Ω_ℓ` is faithful and transitive, with point stabilizers
   `≅ W_(P,ℓ)^ℓ` and at most `ℓ^(ℓ^2)` orbits on ordered pairs. So it is of type (A).
2. So `W_(P,ℓ)`, the simple group `D(W_(P,ℓ))`, and every subgroup of them lie in `B_A`. For
   `ℓ = 2`, `Ω_2` is the set of pairs `(U, X ∖ U)`, and this is the clopen action of
   `fp-clopen-transitive-full-cantor-groups-have-type-a-actions`.
3. (SQ) and (JE) follow for these hosts: `D(W_(P,ℓ)) x D(W_(P,ℓ))`, and `D(W_(P,ℓ)) x G` for
   any `G ∈ B_A`, embed in finitely presented simple groups.

## Proof

**Cylinders.**
- A cylinder is `Z = (c + ℓ^k Z_ℓ^T) x Z_ℓ^(D∖T)`, with `T ⊆ D` finite and `c ∈ Z^T`.
- Every clopen set is a finite disjoint union of cylinders.
- `μ(Z) = ℓ^(−k|T|)` has class 1, since `ℓ ≡ 1` modulo `ℓ − 1`. So the class of `U` is the
  number of cylinders in any decomposition, modulo `ℓ − 1`.

**Allowed maps.**
- `a_Z : X → Z`, `x ↦ (c + ℓ^k x_T, x_(D∖T))` is one allowed piece, with `M = ℓ^k I`, `b = c`
  and `f = id`.
- For a fixed coordinate `d` and `0 <= j < ℓ`, the pieces `x ↦ (ℓ x_d + j, x_(D∖{d}))` map `X`
  onto the `ℓ` cosets `x_d ≡ j (mod ℓ)`, which partition `X`.
- An allowed piece multiplies `μ` by `|det M|_ℓ ∈ ℓ^Z`, so it maps a cylinder onto a clopen set
  of class 1.

**(a) Equal classes are joined by allowed-piecewise maps.**
- Let `U` and `U'` be nonempty clopen sets of equal class, made of `m` and `m'` cylinders, so
  `m ≡ m'` modulo `ℓ − 1`.
- Replacing one cylinder `Z` by the `ℓ` cylinders `a_Z(x_d ≡ j)` raises the count by `ℓ − 1`.
  So we may assume `m = m'`.
- Match cylinders by `a_(Z') ∘ a_Z^(-1)`. This is affine on `T ∪ T'`, with diagonal
  `ℓ`-power linear part and translation in `Z[1/ℓ]`, so it is allowed.

**(b) Allowed pieces are `W`-local.** Let `p : Π → Π'` be an allowed piece and `x ∈ Π`.
- Choose a cylinder `Z ∋ x` with `Z ⊊ Π`. Then `p(Z) ⊊ Π' ⊆ X`, and `p(Z)` has class 1.
- So `X ∖ Z` and `X ∖ p(Z)` are nonempty clopen sets of class 0. By (a) they are joined by
  an allowed-piecewise map.
- Gluing it to `p|_Z` gives a piecewise-allowed homeomorphism of `X`. By definition that is
  an element of `W_(P,ℓ)`.

So every allowed-piecewise map between clopen sets agrees near each point with an element of
`W_(P,ℓ)`.

**(c) Fullness.** Let `h` be a homeomorphism of `X` that agrees locally with `W_(P,ℓ)`.
- By compactness, `X` has a finite clopen partition on whose pieces `h` agrees with elements
  of `W_(P,ℓ)`.
- Refine it by their pieces and then into cylinders. The restriction of an allowed piece to a
  smaller cylinder is allowed.
- So `h` is piecewise allowed, and `h ∈ W_(P,ℓ)`.

**(d) Restricted copies.** For a clopen `U` of class 1, let `D(U)` be the elements supported in
`U`.
- Take a `W`-local homeomorphism `f : X → U`, from (a) and (b).
- Then `g ↦ f g f^(-1) ⊔ id_(X∖U)` and `k ↦ f^(-1) k f` are inverse isomorphisms between
  `W_(P,ℓ)` and `D(U)`, by fullness. This is the argument of
  `fp-clopen-transitive-full-cantor-group-type-a-proof`.

**(d′) Classes are invariant** (added after the referee). Let `g ∈ W_(P,ℓ)` and let `U` be
clopen.
- Refine `U` into cylinders `Z_1, …, Z_m`, each inside one piece of `g`.
- Each `g(Z_i)` has measure `ℓ^(a_i) μ(Z_i)`, which is again `≡ 1` modulo `ℓ − 1`.
- So `g(U)` has class `m`, the class of `U`, and `W_(P,ℓ)` acts on `Ω_ℓ`.

**(e) The action on `Ω_ℓ`.** `Ω_ℓ` is countable, and nonempty since it contains the cosets of
`x_d` modulo `ℓ`.
- *Transitive:* glue `W`-local maps `U_i → U'_i`, all of class 1, and apply fullness.
- *Stabilizers:* an element preserving each `U_i` is the product of its restrictions, and each
  restriction lies in `W_(P,ℓ)` by fullness. So `Stab(U_1, …, U_ℓ) = D(U_1) x … x D(U_ℓ) ≅ W_(P,ℓ)^ℓ`.
  This is finitely generated because `W_(P,ℓ)` is finitely presented.
- *Pair orbits:* for `((U_i), (U'_j))`, record for each atom `U_i ∩ U'_j` whether it is empty
  and, if not, its class. Two pairs with the same record are related by gluing `W`-local maps
  atom by atom (a), then applying fullness (c). So there are at most `ℓ^(ℓ^2)` orbits.
- *Faithful:* suppose `g ≠ 1`.
  - Pick a cylinder `Z ≠ X` with `gZ ∩ Z = ∅`. `X ∖ Z` has class 0 and consists of `m`
    cylinders, with `m >= 1` and `m ≡ 0` modulo `ℓ − 1`, so `m >= ℓ − 1`.
  - Group the cylinders as `ℓ − 2` singletons and one set of `m − ℓ + 2 >= 1` cylinders. That
    set has class `≡ 1`.
  - The result is a partition `(Z, …) ∈ Ω_ℓ` that `g` moves.
- *Type (A):* `W_(P,ℓ)` is finitely presented (item 1 of the required node), so the BFFHZ
  conditions hold.

**Items 2–3.** `B_A` is closed under subgroups and finite direct products
(`boone-higman-type-a-class-closed-under-finite-extensions`), and its members embed in finitely
presented simple groups. ∎

## Lesson for general BH

A finite `K_0`-type invariant on clopen sets never blocks the permutational form. Act on
ordered partitions of the space into pieces of its own class, instead of on clopen sets. The
proof uses only four things:
- fullness;
- finitely many local-equivalence classes of clopen sets;
- arbitrarily small clopen sets of the unit class;
- a partition into `k >= 2` pieces of the unit class.

It is the Higman–Thompson `V_(ℓ,r)` trick in `B_A` form. With
`projective-leavitt-tensor-units-lie-in-the-permutational-class`, it shows that on both host
machines of the graph, full groups and Leavitt-tensor unit groups, PBH is exactly finite
presentation of the host.

## Referee (bh-ref-misc, 2026-09-18): PASS given finite presentation of `W_(P,ℓ)`

Internal referee lane, not an external review. The definition of `W_(P,ℓ)` was read in
`twisted-s-integral-affine-groups-are-fp-and-virtually-simple`:
- it is the group of all homeomorphisms of `X` that are piecewise affine over `Z[1/ℓP]` on cosets of
  open subgroups, up to coordinate permutations from `F`;
- so it is full by definition, which justifies (b) and (c).

**Checked.**
- **The allowed maps.** `a_Z` is allowed, with `M = ℓ^k I` and `b = c`. The composites
  `a_(Z') ∘ a_Z^(-1)` are affine on `T ∪ T'`, with a diagonal `ℓ`-power linear part.
  `|det M|_ℓ ∈ ℓ^Z` and `ℓ ≡ 1 (mod ℓ−1)`, so every class of a cylinder is 1.
- **The count adjustment in (a).**
- **Stabilizers.** They are `D(U_1) × … × D(U_ℓ)`, using (d).
- **The pair-orbit record.** At most `ℓ^(ℓ²)` orbits.
- **Faithfulness.** The `ℓ − 2` singleton cylinders plus one remainder of class `≡ 1` give `ℓ`
  pieces of class 1. For `ℓ = 2` the remainder is `X ∖ Z`.

**Gaps.**
1. **Class invariance** is used but not stated: the action on `Ω_ℓ` needs `W_(P,ℓ)` to preserve
   classes. It does, because each piece scales `μ` by a power of `ℓ` (refine `U` into cylinders
   inside pieces).
2. **Notation.** In (b), `P` names a piece and also the set of primes.
3. **Status.** Everything rests on item 1 of `twisted-s-integral-affine-groups-are-fp-and-virtually-simple`
   (`W_(P,ℓ)` finitely presented). That item is an unreviewed, load-bearing lane proof, marked
   "referee review requested". Until it passes, the (SQ) and (JE) conclusions for `W` and `W_(P,ℓ)` are
   conditional on it.
