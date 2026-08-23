---
rg: 2
id: depthwise-opnorm-mf-radical-proof
kind: route
title: Take the corona-coordinate limit before the challenge-depth limit
target: depthwise-opnorm-collapse-implies-mf-radical
requires:
  - countable-group-mf-conventions
---

Let

```text
Theta:Gamma -> U(product_n M_(d_n)(C) / directSum_n M_(d_n)(C))
```

be any norm-corona homomorphism.  Choose unitary lifts `U_n(s)` of the
finitely many generator images.  Fix `N`.  Every relator in the finite set
`R_N` is the identity in `Gamma`, hence

```text
Def_(R_N)(U_n)->0.
```

Applying `(DOC1)` coordinatewise gives

```text
limsup_n ||w(U_n)-I||_op <= b_N.
```

This holds for every fixed `N`.  Since `b_N->0`, the marked word converges to
the identity in operator norm, so `Theta(w)=1`.  The homomorphism `Theta` was
arbitrary; therefore `w` lies in `Res_MF(Gamma)`.
