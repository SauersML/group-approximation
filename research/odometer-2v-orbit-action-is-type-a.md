---
rg: 2
id: odometer-2v-orbit-action-is-type-a
kind: claim
title: The odometer group 2V_tau acts on the orbit of (0^∞,0^∞) with type [A_2], so its twisted Brin–Thompson group is a finitely presented simple group in which BS(1,2) has an infinite-entropy base
distinct_from:
  odometer-2v-is-fp-simple-and-contains-bs12: that proves 2V_tau is finitely presented, simple and contains BS(1,2) acting on C × C with finite entropy; this is about the permutation action of 2V_tau on one countable orbit, and the twisted Brin–Thompson group built from it.
  equicontinuous-bs-bases-force-conjugator-entropy: that forces zero-entropy BS(1,2) conjugators to avoid free 2-divisible equicontinuous bases in finite-entropy hosts; this produces a finitely presented simple host whose natural Cantor action has a BS(1,2) with an infinite-entropy base, outside the scope of that obstruction.
  fp-simple-highly-transitive-groups-satisfy-pbh: that is BFFHZ Theorem C, which embeds every subgroup of a finitely presented simple highly transitive group in some finitely presented simple twisted Brin–Thompson group with no control over the actor or the dynamics; this names an explicit actor, 2V_tau on an explicit orbit, and controls the entropy of the BS(1,2) base.
artifacts:
  - research/artifacts/gq-bh-bh-testcases-ranking.md
---

**ESTABLISHED** (lane proof, elementary, not independently reviewed; no priority claimed).
Items 2–4 are proved below; item 1 is imported.

## Setting

- `C = {0,1}^N`. `2V_tau = <2V, s>` acts on `C × C`, with `s = tau × id`, where `tau`
  is the 2-adic odometer on the first coordinate (`odometer-2v-is-fp-simple-and-contains-bs12`).
  `u` is the inverse baker map, and `u s u^-1 = s^2`.
- `E ⊆ C` is the set of eventually constant sequences, and `D ⊆ E` the eventually-`0`
  ones. `p = (0^∞, 0^∞)`, and `S = 2V_tau · p`.
- For a group `P` acting faithfully on a countable set `S`, `SV_P` is the twisted
  Brin–Thompson group acting on `C^S`. By `twisted-brin-thompson-finite-presentation-criterion`,
  `SV_P` is finitely presented and simple when `P` is finitely presented, has finitely
  many orbits on 2-subsets of `S`, and has finitely generated point stabilizers.

## Statement

1. **Finite presentation.** `2V_tau` is finitely presented (of type `F_∞`), by
   `odometer-2v-is-fp-simple-and-contains-bs12`.
2. **Finitely many orbits on pairs.** `S ⊆ E × D`, and `2V_tau` has finitely many orbits
   on 2-element subsets of `S`.
3. **Infinite-entropy base.** In the coordinate-permutation action of `2V_tau ≤ SV_(2V_tau)`
   on `C^S`, the element `s` has infinite topological entropy, and `u s u^-1 = s^2`.
4. **Finitely generated stabilizers.** `Stab_(2V_tau)(p)` is finitely generated. Since `S`
   is one orbit, every point stabilizer is.

**Consequence.** By the criterion, `SV_(2V_tau)` is a finitely presented simple group. It contains
`2V_tau`, hence `BS(1,2)`, `Q`, and every group of
`affine-2v-hosts-reach-z-1-2n-by-doubling-but-not-q` that lies in `2V_tau`. In its
natural action on the Cantor set `C^S`, the `BS(1,2)` base `s` has infinite entropy. That
is exactly the regime the finite-entropy obstructions for Higman's group cannot see
(`equicontinuous-bs-bases-force-conjugator-entropy`, item 2; entropy is `0` or `∞` for
a proper-power conjugate).

## Proof of items 2 and 3

**Tails are preserved.** A table element of `2V` changes finitely many leading digits
of each coordinate. The baker-type generators move one leading digit from one
coordinate to the front of the other. In both cases the tail of each coordinate is
unchanged up to a shift. `s = tau × id` changes the first coordinate by adding `1`
2-adically. On `E` this is `x ↦ x + 1`, where an eventually-`0` sequence is a
non-negative integer and an eventually-`1` sequence a negative one. So `s` preserves
`E` and changes the tail of the first coordinate only at `−1 ↦ 0`, and it fixes the
second coordinate. Hence every point of `S` has second coordinate in `D` and first
coordinate in `E`, and `S ⊆ E × D`. Each point of `S` has a *tail type*: `0^∞` or `1^∞`
in the first coordinate.

**`2V` is highly transitive on each tail type.** Let `p_1, …, p_k` and `q_1, …, q_k` be
tuples of distinct points of `E × D`, with `p_i` and `q_i` of the same tail type.
- Write `p_i = (a_i c_i^∞, b_i 0^∞)` and `q_i = (a'_i c_i^∞, b'_i 0^∞)` with
  `c_i ∈ {0,1}`.
- Lengthen the prefixes by repeating `c_i`, and `0` in the second coordinate, until
  the bricks `B_i = C(a_i) × C(b_i)` are pairwise disjoint, the bricks
  `B'_i = C(a'_i) × C(b'_i)` are pairwise disjoint, and neither family covers `C × C`.
- The canonical brick map `B_i → B'_i`, `(a_i w, b_i w') ↦ (a'_i w, b'_i w')`, sends `p_i`
  to `q_i`, since the remaining tails agree.
- The complements of `⋃ B_i` and `⋃ B'_i` are nonempty finite unions of bricks.
  Subdividing a brick raises the number of bricks by one, so both complements can be
  cut into the same number of bricks and matched by canonical maps.
- The result is an element of `2V` sending each `p_i` to `q_i`.

**Finitely many orbits.** Each 2-subset `{x, y}` of `S` has one of three unordered
tail-type patterns. By high transitivity (with `k = 2`), two 2-subsets with the same
pattern lie in one `2V`-orbit. So `2V_tau` has at most three orbits on 2-subsets of `S`.

**Faithfulness.** With `k = 1` the same argument shows `2V` is transitive on `D × D`, so
`S ⊇ D × D` is dense in `C × C`. A homeomorphism fixing a dense set pointwise is the
identity, so `2V_tau` acts faithfully on `S`, as the simplicity half of the criterion
requires.

**Item 3.** `s` acts freely on `C × C`, since `tau` has no periodic points. So every
`s`-orbit `O` in `S` is infinite, and `O ≅ Z` as an `s`-set. On `C^S = C^O × C^(S∖O)`
the element `s` acts as the coordinate shift on `C^O` times a homeomorphism of
`C^(S∖O)`. The projection to `C^O` is a factor map onto the full shift on `C^Z`. That
shift contains the full shift on `n` symbols for every `n` (restrict each coordinate
to `n` points of `C`), so its entropy is at least `log n` for every `n`. Entropy does
not increase under factors (textbook, not re-read at source), so `h(s) = ∞`. The
relation `u s u^-1 = s^2` holds in `2V_tau`, and `2V_tau → SV_(2V_tau)` is a
homomorphism, so it holds in `SV_(2V_tau)`.

## Proof of item 4

Write `Γ = 2V_tau`. By `odometer-2v-is-fp-simple-and-contains-bs12` (its concrete
description), `Γ` is the group of all homeomorphisms of `X = C × C` that, on the
rectangles `C(p_i) × C(w_i)` of some finite partition, have the form
`(p_i x, w_i y) ↦ (p'_i τ^(n_i)(x), w'_i y)`. Put `B_n = C(0^n) × C(0^n)`, a neighbourhood
basis of `p`.

- **Germs.** Let `g ∈ Γ_p = Stab_Γ(p)`. On the rectangle containing `p` we may take
  `p_i = 0^a` and `w_i = 0^b`. Then `g(p) = (p'_i τ^(n_i)(0^∞), w'_i 0^∞) = p` forces
  `w'_i = 0^(b')`, `p'_i = 0^(a')` and `τ^(n_i)(0^∞) = 0^∞`, hence `n_i = 0`, because the
  odometer has no periodic points. So near `p`, `g(0^a x, 0^b y) = (0^(a') x, 0^(b') y)`.
  The germ map `g ↦ (a' − a, b' − b)` is a well-defined homomorphism `Γ_p → Z^2`.
  Refining the rectangle does not change the differences, and composition adds them.
  Its kernel `K_p` is the set of elements equal to the identity on some `B_n`.
- **The pieces are copies of `Γ`.** Let `Γ_(n) = {g ∈ Γ : g|_(B_n) = id}`. The
  complement `U_n = X ∖ B_n` is a finite union of rectangles. Cutting `X` into the same
  number of rectangles gives a homeomorphism `φ : X → U_n` of the allowed form, with all
  `n_i = 0`. For `g ∈ Γ`, the map equal to `φ g φ^-1` on `U_n` and to the identity on
  `B_n` is again piecewise of the allowed form, so it lies in `Γ`. Conversely
  `φ^-1 h φ ∈ Γ` for `h ∈ Γ_(n)`. So `Γ_(n) ≅ Γ`, which is finitely generated.
- **A contracting element.** Let `e ∈ 2V` send `B_1` onto `B_2` by
  `(0x, 0y) ↦ (00x, 00y)`, and `U_1` onto `U_2` by canonical rectangle maps (subdivide
  to match the counts). Then `e` fixes `p` and `e(B_j) = B_(j+1)` for all `j ≥ 1`.
- **Ascending union.** If `g ∈ Γ_(n)` with `n ≥ 1`, put `m = n − 1`. For `x ∈ B_1`,
  `e^m x ∈ B_n`, so `e^-m g e^m x = x`. Hence `e^-m g e^m ∈ Γ_(1)`, and
  `K_p = ⋃_n Γ_(n) ⊆ <Γ_(1), e>`.
- **Conclusion.** `Γ_p / K_p` embeds in `Z^2`, so it is generated by the germs of
  finitely many `g_1, …, g_r ∈ Γ_p`. Then `Γ_p = <Γ_(1), e, g_1, …, g_r>`, and
  `Γ_(1) ≅ Γ` is finitely generated (indeed finitely presented). ∎

## What this does and does not give for Higman's group

- By BFFHZ Theorem C (`fp-simple-highly-transitive-groups-satisfy-pbh`), `H4` embeds in
  some finitely presented simple twisted Brin–Thompson group if and only if `H4` has
  the permutational Boone–Higman property. So an `SV_P` host for `H4` is the same
  problem as a type (A) actor containing `H4`. This node does not solve it.
- What it adds is a concrete finitely presented simple host where a
  proper-power conjugate can have infinite entropy. That makes it a place to look for
  the `H4` four-cycle outside every finite-entropy obstruction. Generators inside
  `P = 2V_tau` itself would mean `H4 ≤ 2V_tau`. That is open, and constrained by the
  finite-entropy obstructions, because `2V_tau` acts on `C × C` with finite entropy. The
  new room is elements of `SV_P` outside `P`, which mix coordinate labels with brick
  maps. A single coordinate label with only finitely many infinite orbits is not
  conjugate to its square in `SV_P` (heuristic recorded on
  `higman-group-satisfies-boone-higman`). `s` escapes this: it fixes the second coordinate, and
  distinct second coordinates give distinct `s`-orbits, so it has infinitely many
  infinite orbits on `S`.
