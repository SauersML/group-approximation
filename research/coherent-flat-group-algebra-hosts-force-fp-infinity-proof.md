---
rg: 2
id: coherent-flat-group-algebra-hosts-force-fp-infinity-proof
kind: route
title: Induce the trivial module up, kill its Tor against products by coherence, and descend through the summand
target: coherent-flat-group-algebra-hosts-force-fp-infinity
requires: []
artifacts:
  - research/artifacts/bh-steinberg-hosts-2026-09-12.md
---

Section 4 of the artifact.

**Part 1.**
1. **Reduce to `S`.** For a finitely generated `H <= S`, `K[S]` is free over
   `K[H]` on coset representatives including `1`. So `B` is flat over `K[H]`
   with `K[H]` a summand, and it is enough to treat `S`.
2. **Induce.** `K` is finitely presented over `K[S]`, because `S` is finitely
   generated. So `M = B ⊗_(K[S]) K` is finitely presented over `B`.
3. **Kill Tor.** By flat base change,
   `Tor_k^(K[S])(Π B, K) = Tor_k^B(Π B, M)`. This vanishes for `k >= 1`, because
   `Π B` is flat by Chase.
4. **Descend.** `Π K[S]` is a summand of `Π B` as a right `K[S]`-module, so
   `Tor_k^(K[S])(Π K[S], K) = 0` for `k >= 1`. With finite presentation of `K`,
   the Bieri--Eckmann criterion gives `FP_infinity`.

**Part 2.** `Ext^i_(K[S])(K, Res W) = Ext^i_B(M, W)` for `B`-modules `W`, by
Shapiro, and this vanishes for `i > pd_B M`. Every `K[S]`-module `N` is a
summand of `Res Hom_(K[S])(B, N)` when `K[S]` is a bimodule summand of `B`.

**`Z wr Z`.** Write `Z wr Z = A ⋊ Z` with `A` free abelian on the `e_i`.
- The LHS spectral sequence has only the columns `p = 0, 1`, so
  `H_0(Z; H_2(A;K))` injects into `H_2(Z wr Z; K)`.
- The shift permutes the basis `e_i ∧ e_j` (`i < j`) freely, with infinitely many
  orbits, so the coinvariants are infinite-dimensional.
- Type `FP_2(K)` would make `H_2` finite-dimensional.
