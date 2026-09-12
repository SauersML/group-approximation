---
rg: 2
id: dihedral-sampling-margin-makes-positive-lift-trivial
kind: claim
title: A curvature-scale dihedral margin makes the positive lift trivial
distinct_from:
  moving-dihedral-quotients-force-linear-positive-lift-extent: that gives extent-two examples whose margin is of order N^(-2) and whose positive lifts need linear extent; this gives the matching positive regime above the curvature scale.
  sl2z-central-split-inherits-operator-fejer-riesz: that factors an already positive polynomial on a modular vertex; this supplies an explicit condition under which quotient positivity implies the required upstream positivity.
  finite-nuclear-quotient-does-not-complete-partial-toeplitz-data: that obstructs operator-valued completion with no global polynomial margin; this proves a positive lift when a quantitative global sampling margin is present.
---

Let

```text
W=C2*C2=<s,t>,       w=st,
H_N=W/<<w^N>>,       q_N:C[W]->C[H_N].
```

Let `E` be finite dimensional and consider a selfadjoint
operator-valued rotation polynomial

```text
p=sum_(k=-d)^d P_k tensor u_w^k,
P_(-k)=P_k*,
K_2(p)=sum_(k=-d)^d k^2 ||P_k||.                       (DSM1)
```

If

```text
q_N(p) >= mu I                                         (DSM2)
```

in `B(E) tensor C*(H_N)`, then the same algebraic representative upstairs
satisfies

```text
p >= (mu-pi^2 K_2(p)/(2N^2)) I                         (DSM3)
```

in `B(E) tensor C*(W)`.

In particular, if

```text
mu >= pi^2 K_2(p)/(2N^2),                              (DSM4)
```

then no relation-ideal correction is needed: `p` itself is a positive
lift of `q_N(p)`, with rotation degree `d` and free-product syllable
extent at most `2d`. The operator-valued Fejer--Riesz theorem on
`C2*C2` then factors it with factor extent at most `d+1`.

The scale `N^(-2)` is unavoidable. For the scalar extent-two family in
`moving-dihedral-quotients-force-linear-positive-lift-extent`,

```text
mu_N=(1-cos(pi/N))/2 asymptotic to pi^2/(4N^2),
```

and the same representative is negative upstairs. Thus a uniform
quotient-to-free-product lifting theorem can only operate with a
quantitative positivity margin, or with additional relation-specific
structure. Pure positivity at the moving quotient boundary has no
uniform extent lift.

This lemma does not solve the Iwahori selector: the bounded dual and Choi
constraints are semidefinite and need not have a uniform strict margin.
It identifies exactly why adding such a margin would change the problem.
The nonhyperlinear-group root remains open.

DERIVATION
dihedral-sampling-margin-positive-lift-proof
