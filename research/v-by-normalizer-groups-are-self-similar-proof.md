---
rg: 2
id: v-by-normalizer-groups-are-self-similar-proof
kind: route
title: Restricting a bi-synchronizing homeomorphism to an invariant cone keeps its core, and V absorbs the non-cone images of cones
target: v-by-normalizer-groups-are-self-similar
requires:
  - v-normalizer-rsgs-contract-iff-finite-outer-order
artifacts:
  - research/artifacts/gq-gq-infinite-primes-out-v-reading.md
---

**Item 1.** Let `g ∈ G`, `g(C_u) = C_u`, and `g_u = e_u^{-1} g e_u`, a homeomorphism of `C`.
- Its minimal transducer consists of the states of the transducer of `g` reachable after
  reading `u`. That is synchronizing at the same level, and so is the transducer of
  `g_u^{-1} = e_u^{-1} g^{-1} e_u`.
- So `g_u` is bi-synchronizing, and by BCMNO it lies in `N(V)`. Its core is the core of `g`,
  because the core consists of the states reached at arbitrarily long words, and those are
  the same.
- By BCMNO the core determines the class in `O_2 ≅ Out(V) = N(V)/V`. So `g_u ∈ gV ⊆ G`,
  since `V ≤ G`.

**Item 2.** `ι_u(g)` agrees on `C_u` with `e_u g e_u^{-1}`. Near a point `ux`, `g` is locally a
composite of prefix maps with `g`, and the prefix maps `x ↦ ux` and back are locally in `V`. So
`ι_u(g)` locally agrees with `v g v'` for suitable `v, v' ∈ V`; off `C_u` it is the identity.
Hence `ι_u(g) ∈ [[G]]`. Multiplicativity is immediate from the definition.

**Item 3.** Let `h ∈ [[G]]`. By compactness there is a complete prefix code `{u_i}` and
`k_i ∈ G` with `h = k_i` on `C_{u_i}`. The sets `D_i = h(C_{u_i})` form a clopen partition of `C`
into `r` nonempty pieces. `V` acts transitively on ordered clopen partitions with `r` nonempty
pieces: write each piece as a finite union of cones and match cones by prefix maps. So there
is `w ∈ V` with `w(C_{u_i}) = D_i` for all `i`. Then `w^{-1} h` preserves each `C_{u_i}` and equals
`w^{-1} k_i ∈ G` there. Since `w^{-1} k_i` is a bijection of `C` mapping `C_{u_i}` onto itself, it lies in `G` and preserves `C_{u_i}`, so by item 1
`g_i := e_{u_i}^{-1} (w^{-1} k_i) e_{u_i} ∈ G`. So `w^{-1} h = ∏ ι_{u_i}(g_i)`. Every cone copy `ι_u(g)` is `c ι_0(g) c^{-1}`
for any `c ∈ V` that maps `C_0` onto `C_u` by `0x ↦ ux`. So `[[G]] = ⟨V, ι_0(G)⟩`. For
`G = V⟨t⟩`, `ι_0(V) ≤ V`, so `[[G]] = ⟨V, ι_0(t)⟩`.

**Item 4.** If `w ∏ ι_{u_i}(g_i) = 1`, then `w = ∏ ι_{u_i}(g_i)^{-1}` preserves each `C_{u_i}`, and
there it equals the cone copy of `g_i^{-1}`. The restriction of `w ∈ V` to an invariant cone,
conjugated back by `e_{u_i}`, is an element `v_i ∈ V`. So `g_i^{-1} = v_i`, and `w = ∏ ι_{u_i}(v_i)`.
The converse is immediate. ∎
