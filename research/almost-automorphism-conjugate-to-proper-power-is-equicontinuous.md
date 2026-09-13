---
rg: 2
id: almost-automorphism-conjugate-to-proper-power-is-equicontinuous
kind: claim
title: An almost automorphism of a regular rooted forest that is conjugate to a proper power of itself generates an equicontinuous group, and has finite order if it lies in V_{d,r}; so BS(k,l) with |k| ≠ |l| embeds in no Higman--Thompson group
distinct_from:
  kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf: that constrains Kazhdan subgroups of Rover--Nekrashevych groups through a commensurated set; this constrains single elements conjugate to proper powers, in the larger group of all almost automorphisms, through an exponent cocycle.
  baumslag-gersten-odometer-pieces-force-fixed-points: that analyses b-invariant minimal equicontinuous pieces of a; this proves that an element conjugate to a proper power of itself is equicontinuous on the whole Cantor space.
artifacts:
  - research/artifacts/bh-bg-similarity-hosts-2026-09-12.md
---

**ESTABLISHED** (elementary; no novelty claimed).

**Setting.**
- Let `Σ` be an alphabet with `d ≥ 2` letters, and let
  `X_{d,r} = {1,…,r} × Σ^N`.
- A *cone* `C(u)` is the set of points that begin with a finite word `u`, made
  of a root and a digit string.
- The group `A_{d,r}` of *almost automorphisms* consists of the homeomorphisms
  `g` of `X_{d,r}` with the following property. There are two partitions
  `X_{d,r} = ⊔ C(u_i) = ⊔ C(v_i)` into cones, and tree automorphisms `g_i`,
  such that `g(u_i w) = v_i g_i(w)`.
- `A_{d,r}` contains the Higman--Thompson group `V_{d,r}` (all `g_i = 1`). It
  also contains every Röver--Nekrashevych group `V_{d,r}(G)`, for any
  self-similar `G`.

**Statement.** Let `g, f ∈ A_{d,r}` with `f g^k f^-1 = g^l`, where `k, l ≠ 0`
and `|k| ≠ |l|`. Then:
1. there are `N` and `K` such that, for every `m ∈ Z` and every word `q` with
   `N` digits, `g^m` acts on `C(q)` as `q w ↦ p h(w)`, where `h` is a tree
   automorphism and `||p| - N| ≤ K`. In particular every `g^m` is
   `2^K`-Lipschitz on level-`N` cones, so `<g>` is equicontinuous;
2. some `g^j` with `j ≥ 1` maps every level-`N` cone onto itself;
3. if `g ∈ V_{d,r}`, then `g` has finite order.

**Consequence.** Let `BS(k,l) = < s, u | u s^k u^-1 = s^l >` with
`|k| ≠ |l|`. Every homomorphism `BS(k,l) → V_{d,r}` sends `s` to an element of
finite order. So `BS(k,l)` embeds in no `V_{d,r}`, and in particular in none of
`V`, `T` or `F`.

**Scope.**
- *What is not new.* Non-embedding of `BS(k,l)` in `V_n` also follows from the
  undistortedness of cyclic subgroups of `V_n`. That result is stated in the
  abstract of arXiv:1107.0672, checked from source.
- *What this node adds.* Items 1 and 2 for elements with tree-automorphism
  sections, and the finite-order conclusion for non-injective maps. These are
  what `baumslag-gersten-embeds-in-no-rover-nekrashevych-group` uses.
- *What this node does not cover.* Brin--Thompson groups `nV`, rational
  similarity groups, and shifts of finite type with several cone types.

The proof is `almost-automorphism-exponent-pumping-proof`.
