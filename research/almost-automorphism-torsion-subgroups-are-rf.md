---
rg: 2
id: almost-automorphism-torsion-subgroups-are-rf
kind: claim
title: Every finitely generated torsion subgroup of the almost automorphism group of a rooted regular tree is residually finite, so these groups, all Higman–Thompson groups and all Röver–Nekrashevych groups contain no infinite finitely generated group of finite exponent
distinct_from:
  restricted-burnside-finiteness: that is Zelmanov's theorem that finitely generated residually finite groups of finite exponent are finite; this proves residual finiteness of finitely generated torsion subgroups of one large class of Cantor homeomorphism groups, which is what lets Zelmanov's theorem be applied there.
  fp-self-similar-groups-embed-in-fp-simple-groups: that embeds self-similar groups G in finitely presented simple Röver–Nekrashevych groups V_d(G); this bounds the torsion subgroups of every V_d(G), for every self-similar G, including G that are not finitely generated or not contracting.
  kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf: that shows Kazhdan (FW) subgroups of V_d(H) virtually embed in H^n, via commensurated sets; this gets the same conclusion shape for finitely generated torsion subgroups, via the depth cocycle, in the larger almost automorphism group.
  almost-automorphism-conjugate-to-proper-power-is-equicontinuous: that uses the same exponent cocycle and a pumping lemma for one element conjugate to a proper power of itself; this uses a pushdown pumping over a whole finitely generated torsion subgroup.
  decidable-fp-groups-need-not-embed-in-rational-group: that excludes some decidable inputs from rational homeomorphism groups by word-problem complexity; this excludes every infinite finitely generated group of finite exponent from almost automorphism groups by a residual-finiteness argument, with no complexity input.
---

**ESTABLISHED (2026-09-18)** through `almost-automorphism-torsion-subgroups-are-rf-proof`.
Lane proof (bh-free-12), elementary, not independently reviewed. Inputs: Zelmanov's positive solution of the
restricted Burnside problem (`restricted-burnside-finiteness`, cited) for the corollary only. No priority is
claimed: a bounded arXiv abstract search (2026-09-18) found no statement of it; the case G = 1 is Röver's theorem
that V is torsion locally finite (Röver, J. Algebra 220 (1999); cited as Theorem 1.3 in Burillo–Cleary–Röver,
arXiv:1402.3860v2, p. 2, read at source), which the proof recovers.

## Setting

Fix `d >= 2`, the alphabet `X = {0, …, d−1}`, finite words `X*` and the Cantor set `X^ω`. For a word `p`, the
cone `[p]` is the set of infinite words beginning with `p`. `Aut(X*)` is the group of automorphisms of the rooted
d-ary tree; it is self-similar: `g(a w) = g(a) g|_a(w)` with sections `g|_a ∈ Aut(X*)`.

The **almost automorphism group** `𝒩_d` is the group of homeomorphisms `h` of `X^ω` for which there are complete
prefix codes `{u_1, …, u_k}` and `{v_1, …, v_k}` and elements `g_1, …, g_k ∈ Aut(X*)` with

    h(u_i w) = v_i g_i(w)   for all i and all w ∈ X^ω.                       (AA)

It contains the Higman–Thompson group `V_d` (all `g_i = 1`) and, for every self-similar `G ≤ Aut(X*)`, the
Röver–Nekrashevych group `V_d(G)` (all `g_i ∈ G`). It is the rooted-tree version of Neretin's group of
spheromorphisms.

## Statement

1. **Main theorem.** Every finitely generated torsion subgroup `H` of `𝒩_d` is residually finite. More precisely,
   for every large enough `n` there is a finite-index normal subgroup `K_n` of `H` that maps each cone of depth `n`
   onto itself, acting there by an element of `Aut(X*)`, and `⋂_n K_n = 1`.
2. **Röver–Nekrashevych refinement.** If `H ≤ V_d(G)` for a self-similar `G`, then `K_n` embeds in `G^(d^n)`, so
   `H` is virtually a subgroup of a finite direct power of `G`. For `G = 1` this gives `K_n = 1`, so every finitely
   generated torsion subgroup of `V_d` is finite (Röver's theorem for `V = V_2`).
3. **Finite exponent.** By Zelmanov (`restricted-burnside-finiteness`), a finitely generated residually finite group
   of finite exponent is finite. Hence **no infinite finitely generated group of finite exponent embeds in `𝒩_d`**,
   hence in no Higman–Thompson group `V_d`, and in no Röver–Nekrashevych group `V_d(G)`, for any `d` and any
   self-similar `G`. In particular no infinite free Burnside group `B(m,n)` embeds in any of them.

4. **Torsion local finiteness transfers.** For a self-similar `G ≤ Aut(X*)`, `V_d(G)` is torsion locally finite (every
   finitely generated torsion subgroup is finite) **if and only if** `G` is. So, for example, `V_d(G)` is torsion
   locally finite for every torsion-free self-similar `G`, and for every self-similar `G` of finite exponent. Röver's
   group, which contains the Grigorchuk group, is not.
5. **Torsion subgroups of Röver's group.** Every finitely generated torsion subgroup of `V_2(𝔊)`, with `𝔊` the first
   Grigorchuk group, is virtually a subgroup of `𝔊^k` for some `k`. In particular it is residually finite and
   virtually a 2-group.

6. **Graph version.** Items 1–3 hold with the rooted tree replaced by the path space `E^∞` of any finite directed
   graph `E` with no sinks. Cones are then `[α]` for finite paths `α`, and pieces are `α w ↦ β g(w)`, where `g` is a
   length-preserving isomorphism between the path trees at the ranges of `α` and `β`, compatible with sections.
   This covers:
   - the Higman–Thompson groups `V_{d,r}`;
   - Matui's topological full groups `V_A` of one-sided irreducible shifts of finite type, where all tails are
     trivial, so f.g. torsion subgroups are finite;
   - Nekrashevych groups of self-similar actions on graphs in the Exel–Pardo sense, for 1-graphs only.

   It does **not** cover higher-rank graphs, so gq-affq's 2-graph group `2V_τ` is not covered. It also does not
   cover groups whose local maps change lengths inside cones, such as general rational similarity groups.
7. **Characterization of the torsion subgroups.** Let `E` be a finitely generated torsion group and `d >= 2`.
   - `E` embeds in `𝒩_d` if and only if some finite-index subgroup of `E` embeds in `Aut(X*)`, the automorphism
     group of the rooted d-ary tree.
   - `E` embeds in some Röver–Nekrashevych group `V_d(G)` (G self-similar) if and only if some finite-index subgroup
     of `E` embeds in some self-similar group `G' ≤ Aut(X*)`.

   So the torsion groups reachable by the Röver–Nekrashevych Boone–Higman hosts are exactly the torsion groups that
   are virtually self-similar.

8. **Non-residually-finite torsion groups.** By item 1, no finitely generated torsion group that is not residually
   finite embeds in `𝒩_d`. Examples:
   - every infinite finitely generated simple torsion group, such as Tarski monsters and Ol'shanskii's infinite
     simple groups of finite exponent;
   - every infinite finitely generated group of finite exponent (item 3).

   So all these Boone–Higman test inputs, including those with solvable word problem, need finitely presented simple
   hosts outside every Röver–Nekrashevych group.

## Why it matters here

The positive BH machinery for self-similar inputs lands in Röver–Nekrashevych groups:
`fp-self-similar-groups-embed-in-fp-simple-groups` (Zaremsky, Thm 1.1) and Belk–Matucci's contracting case. Item 3
shows none of these hosts, nor `V` itself, can serve BBMZ Problem 5.3(6) (free Burnside groups): see
`free-burnside-groups-satisfy-boone-higman` and `fp-simple-groups-can-contain-infinite-finite-exponent-groups`.

## Scope

- The proof uses only that each element is piecewise "prefix replacement followed by a length-preserving tree map
  with sections". It does **not** cover Brin–Thompson groups `nV`, `n >= 2`: there the depth cocycle is a vector,
  and the pumping step fails because different coordinates can pop independently. Whether `2V` contains an infinite
  finitely generated torsion group is not decided here.
- *Remark (not checked):* the same argument should apply to almost automorphisms of the path space of a finite
  directed graph (cones indexed by paths, tail maps length-preserving with sections). Whether the full contracting
  rational similarity groups of Belk–Bleak–Matucci–Zaremsky (arXiv:2309.06224) are of this form was not checked, so
  no claim is made about them.
