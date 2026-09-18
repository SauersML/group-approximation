---
rg: 2
id: domain-exact-hnn-hosts-have-multivalley-kernels
kind: claim
title: If an HNN extension maps to a host HNN extension that is exact on the domain side, every kernel element is hyperbolic with at least two height-maxima per period of its axis
distinct_from:
  ascending-hnn-of-free-groups-satisfy-boone-higman: that is the ascending case, where this lemma gives injectivity outright; this is the general domain-exact case, where it only confines the kernel.
  bh-embeddability-survives-decidable-edge-hnn: that is the open permanence statement; this is a tool that confines what can go wrong for Hall-type hosts.
  finite-index-edge-hnn-embeds-in-fp-simple-group: that uses the HNN subgroup criterion (exact on both sides); this needs exactness on the domain side only.
---

**ESTABLISHED** (lane proof, bh-free-05, elementary, not reviewed). No priority claimed.

## Statement

Let `G = P*_{φ : A -> B}` and `H = Y*_{Φ : C_1 -> C_2}` be HNN extensions, with stable
letters `t` and `s`. Let `P <= Y`, `A <= C_1`, and `Φ|_A = φ`. Let
`θ : G -> H` be the natural map (`P ⊆ Y`, `t -> s`). Assume **domain exactness**:
`P ∩ C_1 = A`. The range side `P ∩ C_2` may be strictly larger than `B`.

Then every `k ≠ 1` in `ker θ` acts hyperbolically on the Bass--Serre tree `T_G`. Its axis is
height-periodic for the height `h : T_G -> Z` induced by `t -> 1`, `P -> 0`, and every period
of the axis contains at least two local maxima of `h`. Equivalently, for no vertex `v` is the
geodesic `[v, kv]` "down, then up".

**Corollary (ascending).** If `A = P`, every vertex of `T_G` has exactly one down-edge, so no
geodesic has a local maximum. Hence `θ` is injective. This reproves the injectivity step of
`ascending-hnn-of-free-groups-satisfy-boone-higman` geometrically. It holds for any vertex
group `P`.

## Proof

1. **The tree map.** `θ` induces a `G`-equivariant, height-preserving map `ψ : T_G -> T_H`.
   The down-edges at `v_0 = P` are indexed by `P/A`, and those at `w_0 = Y` by `Y/C_1`.
   `ψ` sends coset `fA` to `θ(f)C_1`, which is injective iff `P ∩ C_1 = A`. By equivariance
   `ψ` is injective on down-edges at every vertex.
2. **Down-cones.** Let `D(v)` be the union of the descending paths from `v`. Descending paths
   are geodesics. Two distinct points of `D(v)` at the same height have geodesics from `v` that
   leave some last common vertex `u` along distinct down-edges. By step 1 their images leave
   `ψ(u)` along distinct down-edges, and descending paths in a tree with distinct first edges
   end at distinct vertices. So `ψ` is injective on `D(v)`.
3. **Kernel.** Let `K = ker θ`. `K` meets every conjugate of `P` trivially, since `θ` is
   injective on `P`, so `K` acts freely on vertices. `K` preserves height, since
   `θ(k) = 1` has height `0`. If `k ∈ K` and `x ∈ D(v) ∩ D(kv)`, then `k^-1 x ∈ D(v)` and
   `ψ(k^-1 x) = ψ(x)`, so `k^-1 x = x` by step 2, and hence `k = 1`.
4. **Shape.** `D(v) ∩ D(w) ≠ ∅` iff `[v, w]` descends and then ascends: the geodesic lies in
   the union of the two descending paths to a common point. A nontrivial `k ∈ K` is hyperbolic
   (free action without inversions), and `[v, kv]` contains a period of its axis. So no period
   is a single valley. ∎

## Use

For `P` free and `A` of finite index in `P`, the Hall host of
`bh-embeddability-survives-decidable-edge-hnn` (Attempt, bh-free-05) is domain-exact. So a
kernel element would need an axis with at least two valleys per period, each valley folded by
`ψ`. Whether such elements can be ruled out, by a choice of the complement map `α` or of
`F ∩ C_2`, is OPEN. When both edge groups have infinite index, domain exactness is impossible
in any host whose edge groups have finite index in its vertex groups, since `P ∩ C_1` then has
finite index in `P`.
