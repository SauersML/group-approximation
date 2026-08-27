---
rg: 2
id: sofic-nielsen-charts-defeat-uniform-compact-collapse
kind: claim
title: Sofic orbit charts give asymptotic Nielsen models which defeat every pair-uniform compact-collapse modulus
distinct_from:
  finite-dimensional-nielsen-cocycle-models-kill-mark: that kills the marked Nielsen generator in every exact finite-dimensional equivariant model; this constructs finite-dimensional models whose action and covariance defects tend to zero while the same kind of mark stays macroscopically nontrivial
  coordinate-action-not-sofic: that forbids orbit charts for the Kun--Thom pair; this uses a different strict compressor pair whose coset action is established to be sofic, in order to prove that compact recurrence alone has no quantitative dimension-free upgrade
  monomial-ascending-hnn-coset-action-sofic: that establishes the orbit charts for a class of ascending HNN actions; this converts those charts into approximate finite-dimensional models of the affine Nielsen action and computes the marked Hilbert--Schmidt norm
  lamp-coordinate-collision-obstruction: that prices a collision inside a coordinate model; the injective local charts here avoid collisions and use their survival to refute a uniform exact-to-approximate modulus
---

There is a fixed compressor-generated infranormal pair for which the exact
compact-cocycle collapse is maximally discontinuous in normalized
Hilbert--Schmidt norm.  Take

```text
Gamma=EL_3(F_2[x]),       alpha induced by x |-> x^2,
V=<Gamma,t | t gamma t^(-1)=alpha(gamma)>,
X=V/Gamma,                o=Gamma.                         (SNC1)
```

Choose `gamma=e_12(x)`, so `gamma` is not in `alpha(Gamma)`, and put

```text
h=t^(-1) gamma t,         x_*=h o !=o.                    (SNC2)
```

Let

```text
N=F({b_x:x in X-{o}}),    b_o=1,
alpha_g(b_x)=b_(g x)b_(g o)^(-1).                         (SNC3)
```

For every increasing sequence of finite action windows exhausting `V` and
`X`, there are finite-dimensional commutative tracial C-star algebras `B_n`,
maps

```text
beta_n:V -> Aut(B_n),     theta_n:N -> U(B_n),             (SNC4)
```

such that `theta_n` is an exact homomorphism and, on every fixed finite
window,

```text
||beta_n(g)beta_n(k)(theta_n(u))
       -beta_n(gk)(theta_n(u))||_2 ->0,
||theta_n(alpha_g(u))-beta_n(g)(theta_n(u))||_2 ->0.       (SNC5)
```

Nevertheless the strict marked Nielsen generator survives with

```text
||theta_n(b_(x_*))-1||_2 -> sqrt(2).                       (SNC6)
```

Thus there is no modulus `omega(delta)->0`, independent of matrix dimension,
which bounds the marked Nielsen word using only the finite action-table and
covariance defects appearing in `(SNC5)`, even when the compressor pair is
fixed to `(SNC1)`.  In particular, the recurrence step in
`nielsen-cocycle-compactification-proof` cannot itself be made quantitative:
its return time necessarily sees the target model.

## Exact/approximate separation

The pair `(SNC1)` still satisfies the hypotheses of
`finite-dimensional-nielsen-cocycle-models-kill-mark`: `t` compresses
`Gamma`, and `Gamma` together with `t` generates `V`.  Hence every **exact**
finite-dimensional action/covariant representation sends `b_(x_*)` to one.
The sequence `(SNC4)--(SNC6)` therefore gives a literal discontinuity, not
merely a family in which an estimate has poor constants.

This does not refute a modulus using special quantitative rigidity of the
Kun--Thom Kazhdan pair.  Its coset action is nonsofic, so the orbit-chart
construction below is unavailable there.  Any positive Kun--Thom result must
use that extra nonsofic/expanding geometry; compactness and infranormality
alone are insufficient.
