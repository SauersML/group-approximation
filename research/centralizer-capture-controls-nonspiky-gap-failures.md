---
rg: 2
id: centralizer-capture-controls-nonspiky-gap-failures
kind: claim
title: Algebraic centralizer capture kills uniformly non-spiky finite-level gap failures
---

Keep the setup of a Kazhdan group `Gamma`, generator lifts `g_(s,n)`, exact
finite-level centralizers

```text
A_n={g_(s,n):s in S}',
```

and the capture hypothesis

```text
pi(Gamma)' cap M_omega = prod_omega A_n.
```

Fix `C<infinity`.  Decompose `1` into minimal projections `p_(n,j)` of `A_n`.
Call a block `C`-bad if there is a self-adjoint corner-trace-zero witness with

```text
||x||_(2,p)=1,
||x||_op <= C,
sum_s ||[g_(s,n),x]||_(2,p)^2 < kappa^2/4.
```

Then the total normalized trace of the `C`-bad blocks tends to zero along the
ultrafilter.

Thus algebraic centralizer capture controls every finite-level gap failure
whose normalized witnesses have a uniform `L^infinity/L^2` bound.  The
rank-one perturbation no-go shows this is close to sharp: what capture misses
is exactly the possibility that all low-energy mass concentrates on
vanishing-rank tails.  A uniform-integrability / anti-spike theorem for the
almost-central witnesses would upgrade this corrected result to the block-gap
input sought by the normalized-HS Kun programme.
