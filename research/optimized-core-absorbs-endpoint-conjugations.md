---
rg: 2
id: optimized-core-absorbs-endpoint-conjugations
kind: claim
title: Exact-core optimization sharply absorbs the endpoint-conjugation counterpacket
distinct_from:
  endpoint-conjugation-refutes-iwahori-energy: that proves every frozen-core aggregate inverse estimate fails on the conjugation family; this proves that the full exact-core-optimized functional removes precisely that family.
  uniform-gauge-optimized-induced-energy: that asks for one global inequality for arbitrary near endpoints and arbitrary exact cores; this verifies it only on the complete nonlinear orbit obtained by conjugating one exact endpoint through its base commutant.
  gauge-optimized-target-has-uniform-congruence-tangent-gap: that proves a general first-order quotient gap in modular-vertex cochain coordinates; this gives an exact nonlinear zero-section competitor for one otherwise dangerous long-cycle family.
---

Use `G_N` and `E_end` from
`gauge-optimized-induced-energy-target`. Let `(X,R,T)` be any exact
level-`N` square-free endpoint and let `z` be any unitary. Put

```text
X_z=zXz^(-1),               b=(R,T),
c_z=(zRz^(-1),zTz^(-1)).                               (OCA1)
```

Then `c_z` is an exact BS core, the hybrid tuple

```text
U_(c_z)=(X_z,zRz^(-1),zTz^(-1))=z(X,R,T)z^(-1)        (OCA2)
```

is an exact endpoint, and therefore

```text
G_N(X_z,b)<=||zRz^(-1)-R||_2^2
             +||zTz^(-1)-T||_2^2.                    (OCA3)
```

In particular, if `z in {T}'` the second term in `(OCA3)` vanishes. Take
the first-mode family from
`endpoint-conjugation-refutes-iwahori-energy`, with
`z=exp(i epsilon a)` and `g_L=|1-exp(2 pi i/L)|`. Then

```text
G_N(X_z,b)<=epsilon^2 g_L^2.                          (OCA4)
```

For the left regular `N=4^L-1` models, the same conditional-expectation
calculation as in the counterpacket proof gives, for every sufficiently
large odd `L` and all sufficiently small positive `epsilon`,

```text
E_end(X_z,b)>=epsilon^2 g_L^2/16.                     (OCA5)
```

Consequently this entire counterfamily satisfies the desired optimized
estimate with constant `16`, even though its frozen-core inverse-Koopman
energy violates every dimension-free bound. The surviving target is thus
genuinely the quotient by exact-core motion, not a reweighted version of
the refuted frozen-core estimate.
