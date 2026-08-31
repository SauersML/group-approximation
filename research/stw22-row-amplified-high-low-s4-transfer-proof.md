---
rg: 2
id: stw22-row-amplified-high-low-s4-transfer-proof
kind: route
title: Transfer diffuse four-sphere fillings through a rectangular high-low decomposition
target: stw22-diffuse-weighted-copy-uniform-s4-fillings
requires:
  - stw22-diffuse-stiefel-uniform-four-sphere-fillings
  - stw22-diffuse-relative-low-spectrum-five-ball-extension
  - stw22-diffuse-weighted-copy-uniform-s3-fillings
artifacts:
  - research/artifacts/stw22-dim5-factor-bundle-breakthrough-2026-08-31.md
---

Use the exact row amplification in `M_m(N)`:

```text
R(v)=sum_j e_1j tensor v_j,       R(v)^*R(v)=diag(a,...,a).
```

With normalized matrix trace, the normalized `2`-metric in the first-row
corner is exactly the Hilbert-sum tuple metric.  Put

```text
epsilon_0=min(epsilon,1),       eta=(epsilon_0/12)^2,
p_h=1_[eta,1](a),              p_l=1_(0,eta)(a).
```

The high polar row amplifies the weighted input by at most
`eta^(-1/2)`.  Fill its `S^4` at output radius `epsilon_0/3` by the
diffuse Stiefel theorem.  A conservative input radius is

```text
sqrt(eta)rho_(St,4)(epsilon_0/3)/2
 =epsilon_0^3/216000000.                              (W4-1)
```

The low boundary row has fixed diagonal weight `b=ap_l`, lies in the
moving high complement, and satisfies the strict trace reserve required by
the relative five-ball theorem.  Extend the whole row at once.  Unpacking
the row preserves all cross orthogonality relations, and its tuple
displacement is at most

```text
2sqrt(m tau(b))<=2sqrt(eta)=epsilon_0/6.               (W4-2)
```

Recombine high and low parts.  For an arbitrary weighted `S^4`, use global
fourconnectivity of the high Stiefel space and the same relative extension.

