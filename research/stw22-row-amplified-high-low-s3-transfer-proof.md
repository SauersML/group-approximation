---
rg: 2
id: stw22-row-amplified-high-low-s3-transfer-proof
kind: route
title: Transfer the diffuse Stiefel three-sphere modulus through one rectangular row
target: stw22-diffuse-weighted-copy-uniform-s3-fillings
requires:
  - stw22-diffuse-stiefel-uniform-three-sphere-fillings
  - stw22-diffuse-relative-low-spectrum-four-ball-extension
  - stw22-diffuse-weighted-copy-uniform-s2-fillings
artifacts:
  - research/artifacts/stw22-dim4-factor-bundle-breakthrough-2026-08-31.md
---

Use exactly the row amplification from the degree-two route. In
`M_m(N)` with normalized trace `tau_m`, put `e=e_11 tensor 1` and

```text
R(v)=sum_j e_1j tensor v_j.                            (W3-3)
```

For a projection `p`, `P=diag(p,...,p)` has
`tau_m(P)=tau(p)`, while `tau_m(e)=1/m`. A fixed reference frame
`t in eM_m(N)P` identifies the rectangular high-frame space isometrically
with a Stiefel space in the normalized diffuse corner `eM_m(N)e`; its
corner `2`-metric is exactly the tuple Hilbert-sum metric.

Put `epsilon_0=min(epsilon,1)`,

```text
eta=(epsilon_0/12)^2,
p_h=1_[eta,1](a),       p_l=1_(0,eta)(a),
a_h=ap_h,               b=ap_l.                       (W3-4)
```

The boundary high polar row of a weighted `S^3` has distance at most
`eta^(-1/2)` times the weighted input distance. Fill it over `B^4` by
`stw22-diffuse-stiefel-uniform-three-sphere-fillings` at output radius
`epsilon_0/3`, converting back from the corner by `Y |-> Yt`. The required
weighted input radius is

```text
sqrt(eta)rho_St,3(epsilon_0/3)/2
 =epsilon_0^3/216000000.                               (W3-5)
```

Let `H` be that high row and put `f=e-HH^*`. On the boundary the low row
`X=R(vp_l)` satisfies

```text
X^*X=diag(b,...,b),        fX=X,
tau_m(P_h)+tau_m(P_l)=tau(supp(a))<1/m=tau_m(e).       (W3-6)
```

Apply the relative low-spectrum four-ball theorem once in the diffuse
factor `M_m(N)`. It extends the entire low row, retaining every cross-
orthogonality relation. In tuple metric its displacement from the base
low row is at most

```text
2sqrt(m tau(b))<=2sqrt(eta)=epsilon_0/6.               (W3-7)
```

Unpack the first row and add the weighted high and low parts. Equations
(W3-6)--(W3-7) give an exact weighted filling inside the requested ball.

For an arbitrary weighted `S^3`, first use global three-connectivity of
the high Stiefel space and then apply the same relative low extension.
This proves global three-connectivity. Combining all four degreewise
moduli gives equi-`LC^3`.