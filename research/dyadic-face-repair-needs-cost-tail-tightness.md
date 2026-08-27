---
rg: 2
id: dyadic-face-repair-needs-cost-tail-tightness
kind: claim
title: Dyadic face repair closes exactly under repair-cost tail tightness
distinct_from:
  fixed-finite-core-face-has-energy-paid-completion: that proves repair on each fixed finite face with a face-dependent constant; this proves the precise uniform-integrability condition needed to sum those pointwise repairs over moving faces.
  regular-trace-allows-diffuse-dyadic-flow: that gives a conductor-escaping scalar feasibility profile; this shows why conductor truncation cannot provide the repair-cost tail condition required by a diagonal argument.
---

Consider an authenticated orthogonal face decomposition.  For face
`lambda`, let `d_lambda` be its physical dimension, `e_lambda` its
unnormalized relator energy, and suppose exact flexible repair is available
at rank cost

```text
r_lambda <= min(d_lambda,C_lambda e_lambda),          (DFR1)
```

where `C_lambda<infinity` may depend on the finite face.  Put

```text
d=sum_lambda d_lambda,       epsilon=sum_lambda e_lambda/d,
alpha_lambda=d_lambda/d.                              (DFR2)
```

Then, for every `L>=1`, the facewise repairs sum with

```text
sum_lambda r_lambda/d
 <= L epsilon+sum_(C_lambda>L) alpha_lambda.           (DFR3)
```

Consequently `epsilon_n->0` implies a vanishing repaired-rank fraction if

```text
lim_(L->infinity) limsup_n
sum_(C_lambda>L) alpha_(n,lambda)=0.                   (DFR4)
```

For merely pointwise fixed-face moduli, the same conclusion follows from
tightness of the face types.  If `F` is finite and `omega_F(t)->0` is the
maximum of its repair moduli, then for every `theta>0`,

```text
repaired fraction
 <= omega_F(theta)+epsilon/theta
    +sum_(lambda notin F)alpha_lambda.                 (DFR5)
```

Neither pointwise compactness nor dyadic thresholds imply `(DFR4)`.
Abstractly, occupy only type `lambda=n`, take `alpha_(n,n)=1`,
`C_n->infinity`, and normalized energy `e_(n,n)/d_n=1/C_n`.  Total energy
density tends to zero while the pointwise repair law permits repaired
fraction one.  Dyadic regrouping merely rewrites this array.

Thus a qualitative diagonal argument eliminates the soft-delocalized case
only after proving `(DFR4)` or a uniform native completion estimate.
Canonical dyadic congruence characters give the opposite of ordinary type
tightness: every fixed shallow-conductor window has asymptotically zero
mass.  This does not refute `(DFR4)`, since repair cost need not grow with
conductor, but it proves canonical trace and fixed-face compactness alone
cannot establish it.

