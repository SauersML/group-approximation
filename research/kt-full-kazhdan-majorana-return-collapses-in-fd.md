---
rg: 2
id: kt-full-kazhdan-majorana-return-collapses-in-fd
kind: claim
title: The full Kun--Thom Kazhdan packet collapses the mixed Majorana return in exact finite dimensions
distinct_from:
  kt-single-root-majorana-return-finite-countermodels: that constructs exact Clifford matrix models when only one root-stabilizer row is imposed; this proves that the construction fails as soon as the full Kazhdan generating packet is imposed in a genuine finite-dimensional actor representation.
  kt-elementary-kazhdan-packet-rounds-base-lamp: that rounds a nearly stabilizer-central lamp once the Gamma actor is genuine but leaves the return action untreated; this uses finite-dimensional compression invisibility to show that a genuine full actor puts the mixed return itself in the finite Gamma image.
  fd-invisibility-of-compression: that identifies the finite images of the compressed and Laurent elementary groups; this couples that identity quantitatively to the explicit A,B mixed return and the Majorana anticommutation row.
---

**ESTABLISHED.**  Use the pinned `q=2`, `r=d=3` Kun--Thom pair, the
finite elementary Kazhdan packet `K` of
`kt-elementary-kazhdan-packet-rounds-base-lamp`, and the explicit mixed
return

```text
h=L e_12(x_1)L^(-1)=e_12((x_1x_2x_3)^(-1)) in E             (FKM1)
```

from `kt-ab-marked-return-is-the-first-mixed-cylinder`.  Let `kappa_K>0`
be a Kazhdan constant for `K`.  For every genuine finite-dimensional
representation `rho:G->U(D)` and every `X in M_D`,

```text
||[X,rho(h)]||_2
 <= (2/kappa_K) max_(s in K)||[X,rho(s)]||_2.               (FKM2)
```

In particular, if `c=c*=c^(-1)`, `d=rho(h)c rho(h)^*`, and

```text
delta_K=max_(s in K)||[c,rho(s)]||_2,
```

then

```text
||cd+dc||_2 >= 2-(4/kappa_K)delta_K.                        (FKM3)
```

Thus the exact full-packet rows `delta_K=0` force `d=c` and give
`||cd+dc||_2=2`; they are incompatible with the Majorana relation
`cd=-dc`.

This identifies the exact point where the finite-quotient Cliffordization
of `kt-single-root-majorana-return-finite-countermodels` fails.  In every
finite actor quotient the image of `h` belongs to the image of `Gamma`,
while the full packet generates `Gamma`.  A Clifford site fixed by all packet
rows is therefore fixed by `h`, so the proposed returned site is not a new
site and cannot anticommute with the original generator.

The result is deliberately restricted to a **genuine** finite-dimensional
actor representation.  Extending `(FKM2)` to approximate actor matrices with
an error controlled by their normalized-Hilbert--Schmidt relator defect is
exactly the still-open source-specific actor-exactification/collapse gate; no
operator-norm or Frobenius stability transfer is asserted here.

DERIVATION
kt-full-kazhdan-majorana-return-fd-proof
