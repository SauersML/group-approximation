---
rg: 2
id: odometer-2v-orbit-action-is-type-a
kind: claim
title: The odometer group 2V_tau acts on the orbit of (0^∞,0^∞) with type [A_2], so its twisted Brin–Thompson group is a finitely presented simple group in which BS(1,2) has an infinite-entropy base
distinct_from:
  odometer-2v-is-fp-simple-and-contains-bs12: that proves 2V_tau is finitely presented, simple and contains BS(1,2) acting on C × C with finite entropy; this is about the permutation action of 2V_tau on one countable orbit, and the twisted Brin–Thompson group built from it.
  equicontinuous-bs-bases-force-conjugator-entropy: that forces zero-entropy BS(1,2) conjugators to avoid free 2-divisible equicontinuous bases in finite-entropy hosts; this produces a finitely presented simple host (conditional on one gate) whose natural Cantor action has a BS(1,2) with an infinite-entropy base, outside the scope of that obstruction.
  fp-simple-highly-transitive-groups-satisfy-pbh: that is BFFHZ Theorem C, which embeds every subgroup of a finitely presented simple highly transitive group in some finitely presented simple twisted Brin–Thompson group with no control over the actor or the dynamics; this names an explicit actor, 2V_tau on an explicit orbit, and controls the entropy of the BS(1,2) base.
artifacts:
  - research/artifacts/gq-bh-bh-testcases-ranking.md
---

**OPEN**, with one gate. Items 1–3 are proved below (lane proof, elementary, not
independently reviewed; no priority claimed). Item 4 is the open gate.

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
4. **Gate (OPEN).** The stabilizer `Stab_(2V_tau)(p)` is finitely generated.

If item 4 holds, then `SV_(2V_tau)` is a finitely presented simple group. It contains
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

## The gate, item 4

`Stab_(2V_tau)(p)` contains the elements trivial near `p`, a directed union of copies
of `2V_tau`-type groups on complements of shrinking bricks around `p`. It also
contains germ-changing elements at `p`, such as the maps rescaling the cones
`C(0^k) × C(0^l)` around `p`. The expected mechanism is the usual one for `V`: the
germ-changing elements conjugate the "trivial near `p`" part into itself ascendingly,
so finitely many elements generate. This is not proved here. Point stabilizers of
topological full groups may also be reachable from X. Li's finiteness framework
(arXiv:2110.04505), but that was not checked.

## What this does and does not give for Higman's group

- By BFFHZ Theorem C (`fp-simple-highly-transitive-groups-satisfy-pbh`), `H4` embeds in
  some finitely presented simple twisted Brin–Thompson group if and only if `H4` has
  the permutational Boone–Higman property. So an `SV_P` host for `H4` is the same
  problem as a type (A) actor containing `H4`. This node does not solve it.
- What it adds is a concrete finitely presented simple host, modulo item 4, where a
  proper-power conjugate can have infinite entropy. That makes it a place to look for
  the `H4` four-cycle outside every finite-entropy obstruction. The generators would
  have to mix coordinate permutations with infinite orbits and brick maps. A pure
  element of `2V_tau` has finite entropy on `C × C`, and in `SV_P` a single coordinate
  label with finitely many infinite orbits is not conjugate to its square (heuristic
  recorded on `higman-group-satisfies-boone-higman`).
