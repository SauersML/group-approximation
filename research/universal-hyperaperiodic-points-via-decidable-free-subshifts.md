---
rg: 2
id: universal-hyperaperiodic-points-via-decidable-free-subshifts
kind: route
title: A computable point that shows every pattern of a free subshift with decidable language and separated gluing near the origin, infinitely often, is hyperaperiodic and universal at the origin
target: decidable-groups-have-universal-hyperaperiodic-points
requires:
  - decidable-groups-carry-flexible-free-subshifts
---

**Proof (lane proof at design level, bh-g1-simulation, 2026-09-18; unreviewed).**
- The conventions are those of `free-products-with-z-inherit-m2-from-universal-points`.
- The target is stated for finitely presented `A`; this proof needs only finite generation and
  solvable word problem.

## A reformulation (proved here)

For a computable `y`, the pair (H)+(U) is equivalent to three conditions:
- (a) the orbit closure `O(y)` is free;
- (b) `L(y)` is decidable;
- (c) every pattern of `y` occurs outside every ball.

Proof of the equivalence:
- **(H) ⟺ (a).** This is the equivalence stated on the free-product lemma: compactness in one
  direction, and `g = 1` in the other.
- **(U) ⇒ (b), (c).** By (U), `p ∈ L_r(y)` iff `p` occurs at some `g` with
  `r < |g| ≤ R_U(r)`, which is a finite search. Also a radius-`r` pattern at `g_0` lies inside
  the radius-`r'` pattern at `g_0`, which recurs beyond `r'`.
- **(b), (c) ⇒ (U).** Compute the finite set `L_r(y)`. For each `p` in it, search for an
  occurrence at `|g| > r`, which exists by (c). Let `R_U(r)` be the largest distance found.

So universal points are exactly computable **recurrent transitive points of free subshifts with
decidable language**. There is no minimality, and no uniform recurrence.

## Construction

Let `X` be the subshift of `decidable-groups-carry-flexible-free-subshifts`, with
gluing function `G`. Build patterns `p_1 ⊆ p_2 ⊆ …` of `L(X)`, on balls `B(ρ_1) ⊆ B(ρ_2) ⊆ …`.

1. **Samples.** At stage `k`, compute `L_k(X)`, the radius-`k` patterns of the language, which
   is decidable. For each `q ∈ L_k(X)`, choose a centre `g_q` with `ρ_{k−1} + G(ρ_{k−1}+k) < |g_q|`.
   The centres must be pairwise `G(k)` apart and at distance `≥ G(ρ_{k−1}+k)` from `B(ρ_{k−1})`.
   Place a copy of `q` at each.
2. **Commit.** By separated gluing, `p_{k−1}` together with the samples lies in `L(X)`.
   - This is checked by the decision procedure, and the search over centres terminates.
   - Extend to a pattern `p_k ∈ L(X)` on a ball `B(ρ_k)` containing all samples. It is found by
     search, since the current pattern extends.
3. **Limit.** Put `y = ⋃ p_k`. Then `y` is computable: `y(g)` is fixed once `g ∈ B(ρ_k)`.

## Verification

- **`y ∈ X`.** Every window of `y` lies in some `p_k ∈ L(X)`, and `X` is closed.
- **(H).** `O(y) ⊆ X`, and `X` is free.
- **`L(y) = L(X)`.** `⊆` because `y ∈ X`. `⊇` because stage `k` samples all of `L_k(X)`. So
  `L(y)` is decidable.
- **Recurrence.** Every `q ∈ L_r(X)` is sampled again at every stage `k ≥ r`, at distances
  `> ρ_{k−1}`.
- **(U).** Put `R_U(r) = max_q |g_q| + r` over the stage-`r` samples. The samples satisfy
  `r < |g_q|`, and `R_U` is computable. `∎`

## Consequence (the chain, each link a lane proof)

For every finitely generated `K` with solvable word problem:
1. By `clapham-fp-embedding-preserves-word-problem`, `K` embeds in a finitely presented `A` with
   solvable word problem.
2. This route gives a (U)+(H) point on `A`.
3. `free-products-with-z-inherit-m2-from-universal-points` then gives (M2) for `A * Z`, which is
   `decidable-groups-embed-in-fp-groups-satisfying-m2`.
4. `minimal-free-sft-via-m2-overgroups-and-keyed-plane-lifts` gives a minimal free SFT on
   `(A * Z) x Z^2`. That is (P1), `decidable-groups-embed-in-fp-groups-with-minimal-free-sft`.

**Review-critical links.** Three links carry the chain, and all three need a review.
- Lemma (E) of `identifier-markers-give-decidable-free-subshifts`.
- The free-product lemma, a bh-g1-effective lane proof.
- The keyed-slot lift, adapted from Durand–Romashchenko.

**For `GL_n(Q)`.** Take `A = St_10(R_L)`. Then `(St_10(R_L) * Z) x Z^2` is a finitely presented
group containing every `GL_n(Q)` and carrying a minimal free SFT.
- This is not (M2) for `St_10(R_L)` itself.
- The witness on `St_10(R_L)` is a transitive, non-minimal free subshift. It is neither almost
  automorphic nor tree-based; the tree lives only in the overgroup.

## Lesson for general BH

The existence gate needs no minimality anywhere on the input group.
- Minimality comes from the Bass–Serre tree of `A * Z`.
- Finite type comes from a transverse `Z^2` hierarchy with keyed slots.
- The input group supplies only a free subshift with decidable language and gluing. Nested
  identifier markers give one on every decidable group, because greedy marker systems have no
  dead ends past a computable horizon.

With the three links reviewed, E1 (P1) holds for all decidable inputs. The master route would
then be left with rigidity (E2) and finite presentation (E3/P2′).
