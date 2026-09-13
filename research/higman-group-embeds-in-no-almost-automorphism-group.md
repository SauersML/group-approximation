---
rg: 2
id: higman-group-embeds-in-no-almost-automorphism-group
kind: claim
title: Higman's four-generator group has only the trivial homomorphism to any almost-automorphism group of a regular rooted forest, and acts trivially whenever its generators act equicontinuously on a compact zero-dimensional space
distinct_from:
  baumslag-gersten-equicontinuous-generator-acts-trivially: that treats the Baumslag--Gersten group, where the stable letter forces one equicontinuous generator to act trivially; this treats Higman's four-cycle, where each generator is only individually equicontinuous and the smallest-prime descent runs around the cycle.
  higman-four-cycle-intrinsic-mf-seed: that asks for operator-norm collapse of matrix almost-solutions of the four relations; this is an exact statement about homomorphisms into almost-automorphism groups and equicontinuous Cantor actions.
  higman-group-satisfies-boone-higman: that is the open question whether Higman's group embeds in some finitely presented simple group; this excludes every host that lies inside an almost-automorphism group.
artifacts:
  - research/artifacts/ideas-2026-09-13/bh/bh-ec-groups.md
---

**ESTABLISHED** (elementary; no novelty claimed beyond the scope below).

Let `H4 = < g_0, g_1, g_2, g_3 | g_i g_(i+1) g_i^-1 = g_(i+1)^2, i ∈ Z/4 >`, Higman's group. With the other convention, `g_i^-1 g_(i+1) g_i = g_(i+1)^2`, you get the same group after replacing each `g_i` by `g_i^-1`.

**Statement.**

1. **Profinite four-cycle lemma.** Let `T` be a Hausdorff topological group and `h_0, …, h_3 ∈ T` with `h_i h_(i+1) h_i^-1 = h_(i+1)^2` for `i ∈ Z/4`. If each closure `cl<h_i>` is compact and totally disconnected, then every `h_i = 1`.
2. **Equicontinuous actions.** Suppose `H4` acts by homeomorphisms on a compact zero-dimensional metrizable space `X`, and for each `i` the family `{g_i^m : m ∈ Z}` is equicontinuous. Then the action is trivial.
3. **Almost-automorphism hosts.** Every homomorphism `H4 → A_(d,r)` is trivial. Here `A_(d,r)` is the group of almost automorphisms of `X_(d,r)`, as in `almost-automorphism-conjugate-to-proper-power-is-equicontinuous`.

**Consequences.**
- `H4` embeds in no Higman--Thompson group `V_(d,r)`, no Röver--Nekrashevych group `V_(d,r)(G)` (`G` self-similar), and no almost-automorphism group `A_(d,r)`. All of these lie inside `A_(d,r)`.
- So no finitely presented simple group that sits inside some `A_(d,r)` contains `H4`.
- Item 1 is strictly stronger than Higman's theorem that `H4` has no nontrivial finite quotient. It assumes only that each cyclic closure is profinite, not that the closure of the whole image is.

**Scope.**
- *Not covered:*
  - Brin--Thompson groups `nV` with `n ≥ 2`;
  - rational similarity groups;
  - full groups of shifts of finite type with several cone types;
  - any action on a Cantor space in which some generator is not equicontinuous.
- *Sharpness of the cycle.* A single relation of this kind is realizable. `BS(1,2) = < a, b | b a b^-1 = a^2 >` acts faithfully on the 3-adic integers `Z_3` by `x ↦ x+1` and `x ↦ 2x`, and both cyclic closures are profinite. The descent in item 1 uses the fact that the relations close up around the four-cycle.
- *Novelty.* A web search on 2026-09-13 found no statement that Higman's group has only trivial homomorphisms into Neretin-type almost-automorphism groups. The search is not exhaustive.

The proof is `higman-group-almost-automorphism-obstruction-proof`.
