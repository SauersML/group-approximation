---
rg: 2
id: one-opposite-steinberg-relator-does-not-close-laurent-cycle
kind: claim
title: One opposite-cone Steinberg relator does not close the Laurent cycle
distinct_from:
  farey-tree-lift-hits-opposite-steinberg-cycle: that exhibits one cross-cone relation missing from the free cone amalgam; this proves that adjoining that relation still leaves another coordinate relation maximally visible
  opposite-transvections-are-first-nonore-relative-gate: that identifies the full opposite-pair action and RE/C problem; this is a finite exact firewall against solving it with a single cross-cone relator
---

Use the cone amalgam

```text
H=Gamma_+ *_(Gamma_0) Gamma_-
```

from the Farey-tree firewall, and for `i=1,2` put

```text
w_i=[e_12(x_i),e_23(x_i^(-1))]e_13(-1) in H.
```

Then

```text
w_2 notin <<w_1>>_H.                                         (OSR1)
```

In particular, the one-relator quotient `H/<<w_1>>` does not map
isomorphically to the Laurent elementary group: the latter kills both words
by the Steinberg relations.

The separation is finite and exact.  There is a homomorphism

```text
rho:H/<<w_1>> -> EL_r(k)
```

such that

```text
rho(w_1)=1,       rho(w_2)=e_13(-1)!=1.                       (OSR2)
```

Consequently, in the regular representation of the finite group
`EL_r(k)`,

```text
tr(rho(w_2))=0,
||rho(w_2)-1||_2^2=2.                                        (OSR3)
```

Thus one coordinate inverse relation is absorbed without approximation or
dimension growth, while the other remains maximally separated.  Property (T)
of the polynomial vertex groups cannot propagate one cross-cone relation to
the full Laurent packet.

This does not say that the two coordinate relators suffice; the elementary
group functor need not preserve the ring pushout, and further mixed-root or
K-theoretic relations may remain.  It proves the sharp statement needed here:
the explicit word from the first Farey audit is not by itself the full
opposite-slice quotient gate.

DERIVATION
asymmetric-evaluation-separates-opposite-relators-proof
