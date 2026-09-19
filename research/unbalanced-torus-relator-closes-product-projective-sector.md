---
rg: 2
id: unbalanced-torus-relator-closes-product-projective-sector
kind: claim
title: One unbalanced torus relator closes the pure denominator-multiplicity sector of projective transfer
distinct_from:
  balanced-denominator-transport-is-ucp-neutral: that packet satisfies every denominator-balanced relation while retaining a multiplicity twist; this proves that the first explicit unbalanced closure relation charges the resulting projective leak quantitatively.
  two-torus-closures-detect-denominator-multiplicity: that computes the unbalanced word and its exact value on product twists; this combines that computation with exact projective co-density and proves the full trace-square transfer estimate for arbitrary witness unitaries on the product-twist sector.
  projective-trace-square-transfer-for-sl3-pair: that quantifies over every approximate arithmetic assignment, including actor outliers with no product decomposition; this closes only the exact-lattice product-normal-form multiplicity sector.
artifacts:
  - research/unbalanced-torus-product-projective-transfer-proof.md
---

Fix a prime `p` and put

```text
C=SL_3(Z),       A=SL_3(Z[1/p]),
h=diag(p,1,p^(-1)).
```

Let `sigma:A->U(K)` be an exact finite-dimensional representation, let
`V in U(M)`, and on `M tensor K` assign

```text
X_g=I_M tensor sigma(g)       (g in C),
H=V tensor sigma(h).                                      (UTP1)
```

For every `U in U(M tensor K)`, write

```text
q_C(U)=sum_(s in S_C)(1-|tr([U,X_s])|^2),
e_H(U)=1-|tr([U,H])|^2.                                  (UTP2)
```

Let `R_tor` be the fixed two-torus closure word of
`two-torus-closures-detect-denominator-multiplicity`, and put

```text
eta=||ev_(X,H)(R_tor)-I||_2.                             (UTP3)
```

There is a constant `K`, depending only on the fixed Kazhdan generating
set and not on `dim M`, `dim K`, `sigma`, `V`, or `U`, such that

```text
e_H(U) <= K q_C(U)+8 eta^2.                              (UTP4)
```

Here the torus calculation is exact:

```text
eta=||V-I||_2.                                           (UTP5)
```

Thus the coprime congruence packet with an invisible multiplicity twist is
not a counterexample to the full projective-transfer inequality.  Balanced
denominator transport cannot see the twist, but one fixed unbalanced
arithmetic relator pays its trace-square leak with a dimension-free
quadratic bound.

The scope is sharp.  `(UTP4)` assumes that the lattice actor is an exact
amplification and that the only error in the denominator generator is the
single multiplicity factor `V`.  An arbitrary approximate arithmetic actor
need not admit this product decomposition.  Extracting such a coordinate
from a correctable dyadic carrier, or excluding the uniformly
noncorrectable inner-adjoint sector, remains the open part of projective
transfer.
