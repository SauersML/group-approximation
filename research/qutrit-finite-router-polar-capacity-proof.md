---
rg: 2
id: qutrit-finite-router-polar-capacity-proof
kind: proof
title: Combine finite trace capacity with the D8 edge expectation
target: qutrit-any-finite-router-polar-carries-at-most-half-residual
requires:
  - qutrit-external-cyclic-router-selects-only-one-hidden-third
  - jacobson-d8-polar-has-flat-nine-phase-first-row
  - finite-overgroup-packing-preserves-hyperlinearity
---

Take the polar decomposition `X=W|X|` inside the finite-dimensional
von Neumann algebra `C[B]`. The relations `X=p_2XR` imply

```text
W^*W<=R,             WW^*<=p_2.                        (QFC3)
```

A partial isometry has equally traced initial and final projections.
Therefore

```text
tau(W^*W)=tau(WW^*)<=tau(p_2)=1/9.                      (QFC4)
```

This is the finite trace-capacity bound; it uses neither the number of group
words in `X` nor the locations of their double cosets.

It remains to show that coupling to the residual polar cannot amplify this
capacity. Form the group amalgam

```text
G_hat=G *_E B,
```

where `G` is the base containing the qutrit packet and the D8 polar. Let
`E_E` be the canonical trace-preserving conditional expectation from
`C[B]` onto `C[E]`. If `P in C[B]` and `y in C[G]`, reduced-word
orthogonality in the amalgam gives

```text
tau_(G_hat)(P y)=tau_G(E_E(P)y).                        (QFC5)
```

Indeed, after subtracting `E_E(P)`, multiplication by the `E`-part of
`y` still has zero expectation and multiplication by its orthogonal part
is a reduced word of length two.

Apply `(QFC5)` to `P=W^*W` and
`y=f_eta=V_eta V_eta^*`. The expectation `E_E(P)` lies in
`C[E] subset C[F_q]`. The exact D8 support-intersection calculation gives

```text
tau_G(x f_eta)=tau_G(x)tau_G(f_eta)
              for every x in C[F_q],
tau_G(f_eta)=1/32.                                     (QFC6)
```

Since conditional expectation preserves trace,

```text
||W V_eta||_2^2
 =tau(V_eta^*W^*W V_eta)
 =tau(P f_eta)
 =tau(E_E(P))tau(f_eta)
 =tau(P)/32
 <=1/(9*32)
 =1/288.                                               (QFC7)
```

The selected source has

```text
||R V_eta||_2^2=tau(R)tau(f_eta)=(2/9)(1/32)=1/144.
```

Thus `(QFC7)` is exactly one half of the selected mass. The argument
also shows why a finite collection of routers cannot escape by interference:
its polar may rotate the surviving three hidden dimensions inside the six
selected dimensions, but its range remains under the three-dimensional
complementary phase. This completes the universal finite-head no-go.
