---
rg: 2
id: stw22-row-amplified-high-low-s4-transfer-proof
kind: route
title: Transfer the diffuse Stiefel four-sphere modulus through one rectangular row
target: stw22-diffuse-weighted-copy-uniform-s4-fillings
requires:
  - stw22-diffuse-stiefel-uniform-four-sphere-fillings
  - stw22-diffuse-relative-low-spectrum-five-ball-extension
  - stw22-diffuse-weighted-copy-uniform-s3-fillings
artifacts:
  - research/artifacts/stw22-dim5-factor-bundle-breakthrough-2026-08-31.md
---

Use `R(v)=sum e_1j tensor v_j` in the first row of `M_m(N)` with
normalized trace. A fixed reference frame identifies the rectangular high
polar-frame space isometrically with a Stiefel space in the normalized
diffuse corner `e_11M_m(N)e_11`; its metric is exactly the tuple
Hilbert-sum metric.

With `epsilon_0=min(epsilon,1)`, set `eta=(epsilon_0/12)^2` and split the
fixed weight at `eta`. The high polar `S^4` moves by at most
`eta^(-1/2)` times the weighted input distance, so the degree-four
Stiefel theorem fills it over `B^5` at weighted cost `epsilon_0/3` when

```text
delta<=sqrt(eta)rho_St,4(epsilon_0/3)/2
     =epsilon_0^3/216000000.                            (W4-2)
```

The low first-row operator has source `diag(ap_l,...,ap_l)` and lies in
the moving high complement. The relative five-ball theorem fills all
copies at once; its tuple displacement is

```text
2sqrt(m tau(ap_l))<=2sqrt(eta)=epsilon_0/6.            (W4-3)
```

Unpacking and recombining gives the exact weighted filling. Arbitrary high
four-spheres fill by global Stiefel four-connectivity, and the same relative
step proves global four-connectivity of the weighted fibre.