---
rg: 2
id: stw93-saturated-z-slice-null-ideal-proof
kind: route
title: Unique central quasitraces force automatic trace preservation on every copy
target: stw93-all-z-central-slices-generate-quasitrace-null-ideal
requires:
  - stw93-tensor-factor-central-quasitrace-rigidity
---

The canonical tensor-factor embedding belongs to `Theta`, so
`K_Z subset K_Z^sat`.  Fix any `theta in Theta`.  The composition
`tau_omega o theta` is a normalized trace, hence a normalized
`2`-quasitrace, on `F(Z)`.  Uniqueness of the normalized quasitrace on
`F(Z)` forces

```text
tau_omega o theta=tau_(Z,omega).                       (1)
```

Thus every unital homomorphism in `Theta` is automatically trace preserving.
If `x in E`, equation (1) gives

```text
tau_omega(theta(x)*theta(x))=tau_(Z,omega)(x*x)=0.
```

Thus `theta(E) subset I`.  Since `I` is an ideal of `D`, taking all
generators gives `K_Z^sat subset I`.

Fix a normalized `2`-quasitrace `q` on `D` and `theta in Theta`.  The
composition `q o theta` is a normalized `2`-quasitrace on `F(Z)`.  The
Jiang--Su central sequence algebra has a unique normalized quasitrace, namely
its limit trace, by the property-(SI) argument used in
`stw93-tensor-factor-central-quasitrace-rigidity`.  Therefore, without using
any additional hypothesis on `theta`,

```text
q(theta(x)*theta(x))=tau_(Z,omega)(x*x)=0       (x in E). (2)
```

For a bounded `2`-quasitrace, its square-null space

```text
N_q={y in D:q(y*y)=0}
```

is a closed two-sided ideal.  Equation (2), simultaneously for every
`theta in Theta`, places all generators of `K_Z^sat` in `N_q`; hence
`K_Z^sat subset N_q`.  If `k in (K_Z^sat)_+`, hereditary closure gives
`k^(1/2) in N_q`, so `q(k)=0`.  This proves common quasitrace annihilation.

Every normalized quasitrace on `D` now factors uniquely through
`D/K_Z^sat`, while pullback carries a normalized quasitrace on the quotient
to one on `D`.  The two operations are inverse, proving the displayed
bijection.  Because `K_Z^sat subset I`, it identifies vanishing on `I` with
vanishing on `I/K_Z^sat`.  Finally, a singular witness `q,h` from
`stw93-singular-trace-kernel-witness-for-any-negative-answer` has
`q(K_Z^sat)=0<q(h)`, so the image of `h` in the residual quotient is nonzero
for `q` and still witnesses the obstruction.

**Trust boundary.**  The only imported inputs are uniqueness of the
normalized quasitrace on `F(Z)` and the standard null-ideal property of a
bounded `2`-quasitrace.  Automatic trace preservation is proved above; no
abundance, conjugacy, or exhaustion assertion for the family `Theta` is used.
