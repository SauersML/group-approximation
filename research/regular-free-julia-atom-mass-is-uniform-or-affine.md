---
rg: 2
id: regular-free-julia-atom-mass-is-uniform-or-affine
kind: claim
title: Regular free-Julia atom mass is uniform or one affine halfspace
distinct_from:
  regular-trace-blocks-exact-local-predicate-return: that only observes that every selector atom of a retained finite subgroup has positive canonical trace; this computes the exact mass of the free-Julia Gram block on every selector atom and identifies the only possible zero pattern.
  context-word-julia-rows-only-cut-affine-supports: that classifies zero sets produced by context-word return equations on an arbitrary Gram state; this classifies the canonical regular distribution of the Gram state itself, even when the proposed actuator uses noncommuting auxiliaries or several return words.
  universal-central-selector-word-is-affine-for-any-actor: that assumes one ordinary word is scalar on every selector atom; this makes no scalarity assumption and computes a quadratic corner coefficient of the noncommuting word `j`.
---

**ESTABLISHED.**  Let `Gamma` contain involutions

```text
z,j,x_1,...,x_k,
[z,x_i]=[x_i,x_l]=1,
D=<z,x_1,...,x_k> isomorphic to (C_2)^(k+1).            (RFJ1)
```

Work in `L(Gamma)` with its canonical trace.  Put

```text
P_+=(1+z)/2,             P_-=(1-z)/2,
G=P_+jP_-.
```

For a character `chi` of `D` with `chi(z)=+1`, let

```text
q_chi=|D|^(-1) sum_(d in D) chi(d)d.                   (RFJ2)
```

These are the positive-grading joint assignment atoms.  Set

```text
a=jzj.                                                  (RFJ3)
```

Then exactly

```text
||q_chi G||_2^2
 = 1/(2|D|)                         if a notin D,
 = [1-chi(a)]/(2|D|)                if a in D.          (RFJ4)
```

Consequently the canonical Gram distribution on a context has only two
forms.

1. If `jzj notin D`, every assignment atom has the same positive Gram mass.
2. If `jzj in D` and `zjzj!=1`, exactly one affine half of the assignments
   has Gram mass `1/|D|`, and the complementary affine half has mass zero.

The excluded degenerate case `jzj=z` is precisely `zjzj=1`, when `G=0`.

## Universal multi-return consequence

Suppose an attempted nonlinear predicate actuator proves, by a tracially
functorial operator identity or sum-of-squares inequality, that

```text
sum_(chi forbidden)||q_chi G||_2^2
 <= C sum_l ||r_l-1||_2^2,                             (RFJ5)
```

where every `r_l=1` is a defining ordinary-group relator.  Evaluation in the
left regular representation makes the right side zero.  Formula `(RFJ4)`
then forces

```text
jzj in D,
{chi:chi(jzj)=-1} subseteq {allowed assignments}.      (RFJ6)
```

Thus a universal algebraic actuator is possible only when the allowed
predicate contains an affine halfspace, and the one literal element `jzj`
names its defining parity.  This remains true if the left side is paid by
arbitrarily many noncommuting auxiliary rows: only tracial functoriality of
the final inequality is used.

For `R_*` after imposing its honest odd-parity affine hull, `(RFJ6)` is
exactly selection of one of the seven four-point maximal Fano caps.  Before
imposing odd parity, no eight-point affine halfspace fits inside the
seven-point predicate, so no universal algebraic actuator exists at all.

Across several contexts the conjugate `jzj` is the **same group element**.
If `(RFJ5)` is universal for every context, then it must belong to every
context subgroup `D_c` and be represented there by a parity whose negative
halfspace is allowed.  Hence a tracially functorial free-Julia actuator does
not evade the deterministic-parity/Fano-cap gate; it strengthens it to one
common conjugate represented in every context.

Therefore the open actuator in `free-julia-nonlinear-predicate-actuator`
must be genuinely finite-matrix/canonical-approximation-specific.  A fixed
operator identity, positive group-algebra SOS, or finite-von-Neumann
inequality cannot close it unless the exact perfect source already admits
the displayed affine-halfspace restriction.
