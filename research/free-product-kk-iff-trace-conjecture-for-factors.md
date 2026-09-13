---
rg: 2
id: free-product-kk-iff-trace-conjecture-for-factors
kind: claim
title: C*_r(G * H) has projections of exactly the traces (tau K_0(G) + tau K_0(H)) in [0,1], so Kadison--Kaplansky for G * Z is the trace conjecture for G
distinct_from:
  fractional-matrix-trace-gives-projection-in-g-star-z: that gives one direction (a trace defect over G yields a projection over G * Z); this computes the full set of projection traces of C*_r(G * H), giving the converse and the exact per-group equivalence.
  reduced-free-product-k0-generated-by-factor-images: that is the K_0 computation; this combines it with strict comparison to decide which projections exist.
---

**ESTABLISHED** by `free-product-kk-iff-trace-conjecture-for-factors-proof`.

**Theorem.** Let `G, H` be nontrivial countable groups, not both `C_2`. Then

```text
{ τ(e) : e a projection of C*_r(G * H) }  =  ( τ_*K_0(C*_r G) + τ_*K_0(C*_r H) ) ∩ [0,1].
```

**Corollaries.** Let `G, H` be torsion-free and nontrivial.
1. `C*_r(G * H)` has no projection other than `0` and `1` iff both `τ_*K_0(C*_r G) ⊆ Z` and
   `τ_*K_0(C*_r H) ⊆ Z`.
2. **Kadison--Kaplansky for `G * Z` is exactly the trace conjecture for `G`.**
3. Kadison--Kaplansky is not known to pass from `G` and `H` to `G * H`: that step needs the trace
   conjecture on the factors. A torsion-free `G` with no nontrivial projection in `C*_r(G)` but a
   non-integer `K_0` trace would satisfy the conjecture while `G * Z` fails it. No such `G` is known.

**Model tests.**
- `F_2 = Z * Z`: `Z + Z = Z`, so no nontrivial projection. This is Pimsner--Voiculescu.
- `PSL_2(Z) = C_2 * C_3`: projections of traces `0, 1/6, 1/3, 1/2, 2/3, 5/6, 1` and no others,
  consistent with its torsion.
- The excluded `D_∞ = C_2 * C_2` is not selfless (`non-dihedral-free-products-are-completely-selfless`).
