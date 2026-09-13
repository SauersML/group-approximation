---
rg: 2
id: free-product-kk-iff-trace-conjecture-for-factors-proof
kind: route
title: Combine the Fima--Germain K_0 generation with strict comparison in the selfless free product
target: free-product-kk-iff-trace-conjecture-for-factors
requires:
  - reduced-free-product-k0-generated-by-factor-images
  - selfless-projection-traces-equal-k0-trace-image
  - non-dihedral-free-products-are-completely-selfless
  - amalgam-torsion-permanence-needs-no-cyclic-reduction
---

Let `A = C*_r(G * H)`.

1. **Selfless.** `(A, τ)` is completely selfless, hence selfless, by
   `non-dihedral-free-products-are-completely-selfless`, since `G, H` are nontrivial and not both `C_2`.
2. **Projection traces.** By `selfless-projection-traces-equal-k0-trace-image`, the projection traces
   of `A` are `τ_*K_0(A) ∩ [0,1]`.
3. **Trace image.** By `reduced-free-product-k0-generated-by-factor-images`,
   `τ_*K_0(A) = τ_*K_0(C*_r G) + τ_*K_0(C*_r H)`. This proves the theorem.

**Corollary 1.**
- *If the factor traces are integral.* Then `τ_*K_0(A) ⊆ Z`. Every projection `e` of `A` has
  `τ(e) ∈ {0,1}`, and since `τ` is faithful, `e = 0` or `1 - e = 0`.
- *If, say, `t ∈ τ_*K_0(C*_r G)` is not an integer.* Then `t - floor(t) ∈ (0,1)` lies in the right
  side, because `-floor(t) = -floor(t)·τ_*[1]` lies in `τ_*K_0(C*_r H)`. So some projection of `A`
  has that trace, and it is neither `0` nor `1`.
- *The group.* `G * H` is torsion-free by `amalgam-torsion-permanence-needs-no-cyclic-reduction`
  (free product = amalgam over the trivial group). So this is a statement about the Kadison--Kaplansky
  root on a torsion-free group.

**Corollary 2.** Take `H = Z`, where `C*_r(Z) = C(T)` and `K_0(C(T)) = Z[1]`, so its trace image is `Z`.

**Corollary 3.** This restates Corollary 1 with `H = Z`; nothing further is claimed.

**Model tests.** `C*(C_n) = C^n` has `K_0 = Z^n`, spanned by minimal projections of trace `1/n`, so
its trace image is `(1/n)Z`. Then `(1/2)Z + (1/3)Z = (1/6)Z`, and its intersection with `[0,1]` is
the listed set. For `F_2` the trace image is `Z + Z = Z`, which recovers the classical absence of
nontrivial projections in `C*_r(F_2)`.
