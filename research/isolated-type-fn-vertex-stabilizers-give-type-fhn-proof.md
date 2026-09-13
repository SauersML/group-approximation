---
rg: 2
id: isolated-type-fn-vertex-stabilizers-give-type-fhn-proof
kind: route
title: "Replace singular cone neighbourhoods by mapping cylinders into (n-1)-connected free complexes"
target: isolated-type-fn-vertex-stabilizers-give-type-fhn
requires: []
artifacts:
  - research/artifacts/zp-fpn-fhn-2026-09-13-part1.md
  - research/artifacts/zp-fpn-fhn-2026-09-13-part3.md
---

Complete proof in Proposition V of
`research/artifacts/zp-fpn-fhn-2026-09-13-part3.md`. It uses Lemma S of
part 1, §1.

1. **The complex `E_v`.** Start from `Lk_v`.
   - Connect it with finitely many `G_v`-orbits of 1-cells, from a base
     vertex to its translates by a finite generating set and to one vertex
     in each orbit of components.
   - The quotient is a finite complex, so it has finitely presented
     `π_1`, mapping onto the finitely presented `G_v`. The kernel is the
     `π_1` of the connected complex and is finitely normally generated.
     Attach finitely many orbits of 2-cells to make it simply connected.
   - For `k = 2, …, n−1`: the current complex `E` is `(k−1)`-connected and
     its chain complex is exact in degrees `≤ k−1`. By Lemma S and `FP_n`,
     `H_k(E)` is finitely generated, and by Hurewicz it is spherical.
     Attaching finitely many orbits of `(k+1)`-cells makes `E` `k`-connected.
2. **Replacement.** Put `A = X ∖ ⋃ int N_v` and `M_v = Cyl(Lk_v ↪ E_v)`,
   and let `Y = A ∪_{⊔ Lk_v} ⊔_v M_v`, done `G`-equivariantly by inducing
   from orbit representatives. `Y` is free with finitely many orbits of
   cells.
3. **Homology.** Mayer–Vietoris for `X = A ∪ ⊔N_v` and `Y = A ∪ ⊔M_v`, both
   along `⊔ Lk_v`. The maps `H_k(N_v) = H_k(pt) → H_k(M_v) = H_k(E_v)` are
   isomorphisms for `k ≤ n−1`. The five lemma gives `H_k(Y) ≅ H_k(X)` for
   `k ≤ n−1`.

Unreviewed.
