---
rg: 2
id: homogeneous-conjugation-invariants-vanish-on-bs-bases
kind: claim
title: Every homogeneous conjugation-invariant quantity vanishes or is infinite on an element conjugate to a proper power, so no proper cocompact CAT(0) group contains Higman's group or the Baumslag--Gersten group
distinct_from:
  brin-thompson-proper-power-conjugates-have-zero-entropy: that is the entropy instance inside Brin--Thompson groups; this is the general lemma for any homogeneous conjugation-invariant quantity, with entropy, asymptotic translation length, stable commutator length and orbit counts as instances, plus the CAT(0) host exclusions.
  equicontinuous-bs-bases-force-conjugator-entropy: that bounds the entropy of the CONJUGATOR from below when the base is equicontinuous; this constrains the BASE through every homogeneous invariant at once.
  type-a-actors-have-no-proper-power-cyclic-edge-splittings: that applies the orbit-count instance to splittings of a type (A) actor; this is the underlying general lemma together with metric and CAT(0) corollaries, and it says nothing about splittings.
  cat0-group-solvable-subgroups-are-virtually-abelian: that is the imported Solvable Subgroup Theorem; this draws the Higman and Baumslag--Gersten host consequences from it and gives an independent translation-length proof.
  higman-group-images-in-nv-force-zero-entropy-bs12-cycles: that constrains homomorphisms into Brin--Thompson groups; this excludes a different host family, the proper cocompact CAT(0) groups, outright.
---

**ESTABLISHED** by `homogeneous-invariants-vanish-on-bs-bases-proof` (lane proof,
elementary, not reviewed; no priority claimed -- the lemma is folklore in each
separate instance, and the value here is the uniform statement and the host
exclusions in items 3 and 4).

## 1. The lemma

Let `G` be a group and let `u, s in G` satisfy

    s u s^-1 = u^n    with  |n| >= 2.

Call a function `nu : G -> [0, infinity]` **homogeneous and conjugation
invariant** when `nu(g h g^-1) = nu(h)` for all `g, h` and `nu(h^k) = |k| nu(h)`
for all `k != 0`. Then

    nu(u) in {0, infinity},

and `nu(u) = 0` whenever `nu` is finite valued. Indeed
`nu(u) = nu(s u s^-1) = nu(u^n) = |n| nu(u)`, and `|n| >= 2`.

## 2. Instances

1. **Asymptotic translation length.** For any isometric action of any group
   `H >= <u, s>` on any metric space `X`, put
   `l(g) = lim_m d(x, g^m x) / m`. It is independent of `x`, conjugation
   invariant, homogeneous, and finite (`l(g) <= d(x, gx)`). So `l(u) = 0`:
   **`u` is never loxodromic.** In a CAT(0) action `u` is elliptic or parabolic;
   in an action on a hyperbolic space `u` is elliptic or parabolic.
2. **Stable commutator length.** If `u in [H, H]` then `scl(u)` is finite,
   homogeneous and conjugation invariant, so `scl(u) = 0`.
3. **Topological entropy.** For a homeomorphism of a compact metric space,
   `h(f^k) = |k| h(f)` and `h` is invariant under topological conjugacy, so
   `h(u) in {0, infinity}`. This is the `h = 2h` step of
   `equicontinuous-bs-bases-force-conjugator-entropy` and the content of
   `brin-thompson-proper-power-conjugates-have-zero-entropy`.
4. **Orbit counts.** The invariant `r(c)` of
   `type-a-actors-have-no-proper-power-cyclic-edge-splittings` (the number of
   infinite `<c>`-orbits, when there are finitely many orbits) is the instance
   `nu = r`.

## 3. No proper cocompact CAT(0) group contains BS(1,n)

Let `Gamma` act properly and cocompactly by isometries on a complete CAT(0)
space. If `u in Gamma` is conjugate in `Gamma` to `u^n` with `|n| >= 2`, then `u`
has finite order. Two proofs, in the route:

- via `cat0-group-solvable-subgroups-are-virtually-abelian`: `<u, s>` would be a
  solvable subgroup that is not virtually abelian;
- directly from item 1: `l(u) = 0`, every element of such a `Gamma` is
  semisimple, so `u` fixes a point, and point stabilizers are finite.

In particular `BS(1,n) = <u, s | s u s^-1 = u^n>` with `|n| >= 2` embeds in no
proper cocompact CAT(0) group.

## 4. Host exclusions for Higman's group and Baumslag--Gersten

Every nontrivial image of Higman's group `H4` contains `BS(1,2)`
(`higman-group-satisfies-boone-higman`, known inputs), and the
Baumslag--Gersten group contains `BS(1,2)`. So by item 3:

- **No group acting properly and cocompactly by isometries on a CAT(0) space
  contains `H4` or `BG`**, and no homomorphism from `H4` into such a group is
  nontrivial.
- Named finitely presented simple groups thereby excluded as hosts for `H4` and
  `BG`: the Burger--Mozes groups and Wise's lattices, which act properly and
  cocompactly on a product of two trees, and every finitely presented simple
  group acting properly and cocompactly on a CAT(0) cube complex. Any
  twin-building lattice whose diagonal action on the product of its two
  buildings is proper and cocompact is excluded as well; whether the finitely
  presented simple Kac--Moody lattices have that property is not checked here.
- This is a new host family for both test cases. The families already excluded
  on main are the residually finite, linear and self-similar hosts, the
  almost-automorphism groups, the piecewise-analytic circle groups, and the
  finite-entropy brick groups.

## 5. Calibration and scope

- **No conflict with Martin's action.** `H4` does act cocompactly on a CAT(0)
  square complex, so the action in item 3 must fail properness: the vertex
  stabilizers of that action are infinite. Item 3 uses properness twice, for
  semisimplicity and for finiteness of point stabilizers.
- **Not an obstruction to Boone--Higman.** `BS(1,n)` itself satisfies
  Boone--Higman (`baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman`), so
  item 3 constrains hosts, not inputs.
- **Textbook inputs**, cited and not re-read in this lane: semisimplicity of
  every element of a proper cocompact CAT(0) action, and homogeneity of
  `scl`. The Solvable Subgroup Theorem route uses only the existing import node.
