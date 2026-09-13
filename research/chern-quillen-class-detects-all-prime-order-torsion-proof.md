---
rg: 2
id: chern-quillen-class-detects-all-prime-order-torsion-proof
kind: route
title: Lift the regular-representation Chern family through the equivariant spectral sequence by p-th powers
target: chern-quillen-class-detects-all-prime-order-torsion
requires: []
artifacts:
  - research/artifacts/hyperbolic-vtf-chern-quillen-persistence-2026-09-12.md
---

Full proof: artifact §§0–2. Outline.

1. **Local family.** Every finite `F` fixes a vertex, so `F <= G_v` and `|F|` divides
   `M`. Since `rho_F|_K = [F:K] rho_K`, naturality and the Whitney formula give
   `res^F_K y_F = y_K`, and conjugation invariance is immediate. The degree-`n` parts
   form a compatible family too.
2. **Value on `Z/p`.** `cbar(rho_{Z/p}) = prod_{i in F_p}(1 + iβ) = 1 - β^(p-1)`,
   using `prod_i (t + iβ) = t^p - β^(p-1) t`. Frobenius gives
   `y_P = (1 - β^((p-1)p^a))^m`, whose degree-`n` part is `-m β^((p-1)p^a) != 0`.
   For `p = 2` use `1 + u^2`.
3. **Spectral sequence.** Order the simplices of the subdivision by inclusion. This
   gives a `G`-equivariant Alexander–Whitney diagonal, so the equivariant cohomology
   spectral sequence
   `E_1^{s,t} = prod_{sigma in Sigma_s} H^t(G_sigma;F_p) => H^{s+t}(G;F_p)`
   (Brown VII.7) is multiplicative. It has `E_1^{s,t} = 0` for `s > d`, and its
   column-`0` edge map is restriction to the vertex stabilizers.
4. **Cycle.** `z = (y_{G_v}^(n))_v` has `d_1 z = 0` by step 1.
5. **Power-lifting.** `n` is even, so `z` is central in `E_r` and
   `d_r(z^p) = p z^(p-1) d_r z = 0`. After `e = max(d-1,0)` Frobenius steps, `z^(p^e)`
   reaches `E_{d+1} = E_infinity`. Any preimage `c in H^N(G;F_p)` satisfies
   `res_{G_v} c = (y_{G_v}^(n))^(p^e)`, and step 1 gives the formula on every finite
   subgroup.
