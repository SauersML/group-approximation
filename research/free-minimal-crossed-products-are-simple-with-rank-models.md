---
rg: 2
id: free-minimal-crossed-products-are-simple-with-rank-models
kind: claim
title: Crossed products of free minimal Z^d Cantor systems over a finite field are simple and carry a faithful Følner rank model
distinct_from:
  minimal-subshift-algebra-is-simple-lef-ring: that proves the Z case is a simple LEF ring through exact periodic models; this gives approximate Følner models for every d, which survive where exact periodic models do not, as for aperiodic Z^2 SFTs.
  leavitt-algebra-has-no-unital-rank-model: that is the non-embedding of the Leavitt algebra into rank ultraproducts; this is the embedding for free minimal crossed products, which is the positive side of the halvable-corner separation.
artifacts:
  - research/artifacts/free-minimal-crossed-product-rings-and-permutive-rigidity-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `k` be a finite field and `Z^d` act freely and minimally on a
Cantor space `X`. Put `R = LC(X, k) ⋊ Z^d`. Then:

1. `R` is simple, `Z(R) = k`, and `Z(EL_m(R)) = EL_m(R) ∩ k^x 1_m` for `m >= 2`.
2. **Følner rank model.** Truncating the orbit representation to boxes `[0, n)^d` gives unital
   rank-approximate homomorphisms. They induce an injective unital homomorphism
   `R -> prod_omega M_(n^d)(k) / {rank-null}`.
3. Hence `R` has a faithful Sylvester matrix rank function, and no matrix amplification of `R` has
   a nonzero halvable idempotent.

The dynamical core of the rank lower bound is minimality, through syndetic visits to a clopen set.

**For the ring route.**
- Every Z^2-SFT crossed product of a free minimal SFT passes the halvable-corner test
  (`halvable-corner-makes-elementary-groups-nonsofic`).
- Finite presentation remains the gate (`sft-crossed-product-fp-iff-quantum-rigid`).

Route: `free-minimal-crossed-products-are-simple-with-rank-models-proof`.
