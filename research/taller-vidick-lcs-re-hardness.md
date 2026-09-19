---
rg: 2
id: taller-vidick-lcs-re-hardness
kind: claim
title: Taller--Vidick give RE-hard constant-answer 3-LCS games with completeness arbitrarily close to one
distinct_from:
  perfect-lcs-gap-implies-nonhyperlinear: that requires exact commuting completeness one; this theorem has completeness only `1-epsilon`, and the loss is essential to its published Fourier decoder.
  fanizza-turing-bcs-signal-collapse: that keeps nonlinear BCS predicates and supplies a projection signal estimate; this outputs only three-variable parity equations and supplies a direct game-value gap.
artifacts:
  - research/artifacts/taller-vidick-lcs-rank-pressure-2026-08-20.md
---

For every rational `0<epsilon<1/72`, Taller and Vidick give a computable
reduction from the halting problem to finite binary LCS games whose equations
contain exactly three variables and whose answers have length three.  On a
halting input the synchronous quantum value is at least `1-epsilon`; on a
nonhalting input it is at most

```text
1-(1/36)(1/sqrt(2))^2 = 71/72.                         (TV1)
```

The quantitative core is their distorted entangled long-code test
`L^epsilon(u,B,pi)`.  For every `epsilon,delta>0`,

```text
omega_q^s(L^epsilon)>=1-(1/36)(1-delta)^2
  => omega_q(G(B,pi)^tensor-u)>=4 epsilon delta^2,       (TV2)
```

while a perfect synchronous source strategy gives

```text
omega_q^s(L^epsilon)>=1-epsilon.                         (TV3)
```

The output is a projection game, so the paper also derives an RE-hardness gap
for unrestricted finite-dimensional quantum value, with a possibly different
constant.  The paper explicitly does **not** prove `(TV3)` with `epsilon=0`;
it notes that such a perfect-completeness result would imply a nonhyperlinear
group.

The loss and soundness use the same random mask `mu`.  Honest loss occurs when
`mu(phi)=-1`, whereas the soundness decoder uses the Fourier damping factor
`(1-2 epsilon)^|beta|`.  Thus the published theorem is not a perfect LCS gap,
but it is a uniform positive-density source of failed three-XOR checks.

Arbitrary finite correlations in the mask do not repair this tradeoff:
`perfect-correlated-masks-have-undamped-conditioned-spectrum` solves the
perfect-completeness linear constraints and shows that they force every
conditioned Fourier coefficient used by the decoder to equal one.
