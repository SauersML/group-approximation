---
rg: 2
id: anchored-flexible-compressions-proof
kind: route
title: Cover the small-codimension Grassmannian and absorb the remaining gauge into the robust pin stabilizer
target: anchored-flexible-compressions-have-zero-entropy
requires:
  - robust-diffuse-pin-stabilizer-has-zero-entropy
---

Write `r_n=m_n-d_n`.  Choose `theta_n->0` so slowly that

```text
(r_n/d_n) log(1/theta_n)->0.                             (AFP1)
```

The Grassmannian of `d_n`-planes in `C^(m_n)` has a `theta_n`-net in
normalized HS distance whose logarithm is

```text
O(d_n r_n log(C/theta_n))=o(d_n^2).                     (AFP2)
```

For every exact class `alpha` and every Grassmannian cell meeting `(AFC1)`,
choose one anchored isometry `V_0`.  If `V` lies in the same cell, the
unitary Procrustes lemma supplies `U in U(d_n)` with

```text
||V-V_0 U||_2=O(theta_n).                               (AFP3)
```

Uniform boundedness then gives, coordinatewise,

```text
V^*X V = U^*(V_0^*X V_0)U+O(theta_n).                  (AFP4)
```

Apply `(AFP4)` to the pin coordinate.  Since both `V` and `V_0` satisfy
`(AFC1)`, the same `U` obeys

```text
||U^*D_n U-D_n||_2 <= 2eta_n+O(theta_n)->0.             (AFP5)
```

By `robust-diffuse-pin-stabilizer-has-zero-entropy`, the possible conjugates
in `(AFP4)` have zero `d_n^2`-normalized covering entropy.  Multiplying their
covering numbers by the `exp(o(d_n^2))` Grassmannian cells and the
`N_n=exp(o(d_n^2))` exact classes still gives `(AFC2)`.
