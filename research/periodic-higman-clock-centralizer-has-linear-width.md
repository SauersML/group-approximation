---
rg: 2
id: periodic-higman-clock-centralizer-has-linear-width
kind: claim
title: The 3-power Higman clock has only linear centralizer width
artifacts:
  - research/periodic-higman-clock-centralizer-has-linear-width-proof.md
distinct_from:
  periodic-higman-bs-clocks-have-three-opnorm-small-seams: that constructs the quantitative operator-norm matcher and leaves its fourth return open; this computes exactly how much right-gauge freedom the clock centralizer supplies for trying to repair that return.
  three-higman-bs-seams-vanish-fourth-is-product-holonomy: that identifies the abstract four-matcher product equation for arbitrary packets; this audits the multiplicity and centralizer size of the concrete q=3^n packet.
  order-four-bs-matcher-builds-higman-opnorm-microstate: that proves a vanishing fourth-return commutator would give a full countermodel; this computes the concrete centralizer in which that return must land.
---

**ESTABLISHED.**  Let `q=3^n`, and let `P` be the permutation unitary on
`C^(Z/qZ)` induced by multiplication by `2^(-1)`.  Its cycle lengths are

```text
L_0=1,                 L_m=2*3^(m-1)  (1<=m<=n).       (HCW1)
```

Consequently the complex vector-space dimension of its matrix commutant is

```text
dim_C {P}' = sum_(a,b=0)^n gcd(L_a,L_b) = 2q-1.        (HCW2)
```

Equivalently, the compact unitary centralizer of `P` has real manifold
dimension `2q-1`.  The largest eigenspace of `P` is its `1`-eigenspace and
has dimension only `n+1`.  For `n>=2`, exactly

```text
L_n-L_(n-1)=4*3^(n-2)=4q/9                           (HCW3)
```

eigenvalues, counted with multiplicity, lie in simple eigenspaces.  By
contrast, the diagonal clock `D` has simple spectrum and its unitary
centralizer is a `q`-torus.

Thus all left/right spectral gauge freedom in a matcher

```text
K in C(D) K_0 C(P)                                    (HCW4)
```

has only `O(q)` parameters, while the ambient unitary group has dimension
`q^2`.  This does **not** prove that the fourth return cannot be repaired:
the equation

```text
K P K^* approximately D,
K^4 P K^(-4) approximately P.                         (HCW5)
```

is nonlinear and could have exceptional solutions.  It does rule out the
suggestion that the visible eigenvalue degeneracies provide an unrestricted
macroscopic commutant capable of absorbing an arbitrary fourth-power
holonomy.  Any repair of `(HCW5)` must exploit the special arithmetic of the
matcher, not merely the size of `{P}'`.
