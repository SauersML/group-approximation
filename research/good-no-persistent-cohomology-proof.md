---
rg: 2
id: good-no-persistent-cohomology-proof
kind: route
title: Factor a continuous profinite cohomology class through one finite quotient
target: good-groups-have-no-persistent-finite-cohomology
requires: []
---

Goodness identifies `alpha` with a class

```text
beta in H^q_cont(G_hat;M).
```

After shrinking inside the kernel of the finite action on `M`, continuous
cohomology is the directed colimit over open normal subgroups `U normal
G_hat` of the cohomology of the finite quotients `G_hat/U`. Hence `beta` is
the inflation of some

```text
beta_bar in H^q(G_hat/U;M)
```

for one open normal `U` acting trivially on `M`.

Put `G_0 = ker(G -> G_hat/U)`. It is normal and finite-index. Under the
comparison map defining goodness, `alpha` is the pullback of `beta_bar`
along `G -> G_hat/U`. On restriction to `G_0` this homomorphism is trivial,
so the pullback factors through `H^q(1;M)=0` because `q>0`. Therefore
`res^G_(G_0)(alpha)=0`.

Goodness passes to finite-index subgroups. Applying the same argument with
any finite-index `H<=G` in place of `G` shows that every element arising at
every stage of the restriction system dies at a later stage; hence the
directed colimit is zero.

Kropholler--Wilkes Theorem 9 says every hyperbolic virtually special group
is good, yielding the final assertion. `QED`
