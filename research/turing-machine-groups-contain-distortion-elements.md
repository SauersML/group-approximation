---
rg: 2
id: turing-machine-groups-contain-distortion-elements
kind: claim
title: "For all n >= 2 and k >= 1 the group of reversible Turing machines RTM(n,k), in particular RTM(2,1), contains an infinite-order element f with |f^N| = O(log^4 N) in a finitely generated subgroup (Callard--Salo, Theorem D), and RTM(n,k) is canonically isomorphic to its moving-tape model RTM_fix(n,k)"
distinct_from:
  brin-thompson-mv-contains-a-distortion-element: that imports Theorem E (a distortion element in mV); this imports Theorem D (a distortion element in every group of Turing machines, including the smallest one RTM(2,1)) together with the moving-tape model and its isomorphism with RTM(n,k), which Theorem E does not state and which is needed to place the element inside a named subgroup of 2V
---

**ESTABLISHED (import)** by `turing-machine-groups-contain-distortion-elements-citation`.

**Statement.**
1. (Moving-tape model, `n = 2`.) Let `k ≥ 1` and let `RTM_fix(2, k)` be the set of homeomorphisms
   `f` of `[[k]] × {0,1}^Z` for which there are a radius `r ≥ 1` and a local rule
   `f_loc : {0,1}^r × {0,1}^r × [[k]] → {0,1}^* × {0,1}^* × [[k]]` whose values
   `(u', v', b)` all have `|u'| + |v'| = 2r`, such that `f(xu.vy, a) = (xu'.v'y, b)` whenever
   `f_loc(u, v, a) = (u', v', b)`. Here `xu.vy` is the point whose coordinates at positions
   `−r, …, −1` read `u` and at positions `0, …, r−1` read `v`. Under composition this is a group,
   canonically isomorphic to the group `RTM(2, k)` of reversible Turing machines of
   Barbieri–Kari–Salo. (The source states this for all `n ≥ 2`, with the local rule written on
   `{0,1}^r`, which is literal only for `n = 2`; only `n = 2` is used here.)
2. (Distortion.) For every `n ≥ 2`, `k ≥ 1`, the group `RTM(n, k)` has a finitely generated
   subgroup `G = ⟨F⟩` and an element `f ∈ G` of infinite order with `|f^N|_F = O(log^4 N)`.
3. (Embedding.) `RTM(n, k)` embeds in the Brin–Thompson group `mV` for all `m ≥ 2`.

The case `n = 2`, `k = 1` of item 2 is the one used downstream
(`lebesgue-preserving-subgroup-of-2v-is-the-turing-machine-group`).
