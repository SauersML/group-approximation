---
rg: 2
id: magnus-embedding-f-over-n-prime-into-wreath-product
kind: claim
title: For a free group F of rank r and a normal subgroup N, the group F/[N,N] embeds in the restricted wreath product Z^r wr F/N
artifacts:
  - research/artifacts/solve-bh-free-solvable-2026-09-13.md
---

**ESTABLISHED (literature import)** through `magnus-embedding-f-over-n-prime-citation`.

**Statement.** Let `F` be free on `x_1, ..., x_r`, let `N` be a normal subgroup of
`F`, and let `G = F/N`. Let `T` be the free left `ZG`-module with basis
`t_1, ..., t_r`. The homomorphism

```text
φ : F -> M(G) = { [[g, t], [0, 1]] : g ∈ G, t ∈ T },     x_i -> [[x_i N, t_i], [0, 1]]
```

has kernel `N' = [N, N]`. So `F/N'` embeds in `M(G)`, and `M(G)` is the restricted
regular wreath product `Z^r wr G`.

**The wreath identification** (hand check). The product
`[[g, t], [0, 1]] [[h, u], [0, 1]] = [[gh, t + g·u], [0, 1]]` gives `M(G) = T ⋊ G`,
with `G` acting on `T` by left multiplication. The map
`Σ_(g, i) n_(g,i) g t_i -> (g -> (n_(g,1), ..., n_(g,r)))` identifies `T` with
`(Z^r)^(G)`. Left multiplication by `h` becomes `(h·f)(g) = f(h^(-1) g)`. So
`M(G) ≅ Z^r wr G`.

**Consumer.** `free-solvable-groups-satisfy-permutational-boone-higman`.
