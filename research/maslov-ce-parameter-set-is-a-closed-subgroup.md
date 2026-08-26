---
rg: 2
id: maslov-ce-parameter-set-is-a-closed-subgroup
kind: claim
title: Connes-embeddable projective regular traces form a closed subgroup of the Maslov circle
distinct_from:
  sp4-fd-projective-multiplier-is-finite: that proves finiteness of multiplier classes having exact finite-dimensional projective representations; this treats asymptotic projective microstates and proves a closed-subgroup dichotomy rather than finiteness.
  sp4-small-maslov-twisted-group-factors-are-ce: that asks for a null sequence of nontrivial CE parameters; this proves that such a sequence forces the entire Maslov circle to be CE.
  deligne-sector-gap-is-exactly-nonhyperlinearity: that focuses on the fixed mod-three parameter; this relates all scalar parameters on the integral Maslov circle by tensor products and limits.
---

**ESTABLISHED.** Let `Gamma=Sp_4(Z)`, fix an integral Meyer--Maslov cocycle
`b in Z^2(Gamma,Z)` generating the free direction, and put

```text
c_theta(g,h)=exp(2 pi i theta b(g,h)),    theta in R/Z.
```

Define

```text
E_CE={theta in R/Z : L_(c_theta)(Gamma) is Connes embeddable}.
```

Then `E_CE` is a closed subgroup of the circle. Consequently exactly one
of the following holds:

```text
E_CE is a finite cyclic subgroup,    or    E_CE=R/Z.      (MCS1)
```

For additivity, take canonical projective microstates `U_g` and `V_g` for
parameters `theta` and `phi`. On tensor products,

```text
(U_g tensor V_g)(U_h tensor V_h)
 approximately c_(theta+phi)(g,h)(U_(gh) tensor V_(gh)),
tr(U_g tensor V_g)=tr(U_g)tr(V_g).                         (MCS2)
```

Thus the tensor tuple has the `c_(theta+phi)`-projective law and canonical
regular trace. Complex conjugation sends a `theta` microstate to a
`-theta` microstate. Hence `E_CE` is a subgroup.

For closedness, suppose `theta_n->theta` and `theta_n in E_CE`. On the
`n`th finite multiplication/moment window, choose a projective microstate
for `c_(theta_n)` with error at most `1/n`. Since `b(g,h)` takes fixed
integer values on that finite window,

```text
max_window |c_(theta_n)(g,h)-c_theta(g,h)| ->0.            (MCS3)
```

The same tuple is therefore a `c_theta`-projective microstate with vanishing
error and the same canonical trace moments. A diagonal sequence proves
`theta in E_CE`. Closed subgroups of the circle are finite cyclic or the
whole circle, proving `(MCS1)`.

In particular, `E_CE` contains nonzero parameters converging to zero if and
only if `E_CE=R/Z`. Therefore the small-twist ISW input is equivalent to
Connes embeddability of **every** Maslov-twisted group von Neumann algebra,
including the mod-three Deligne algebras. If the small-twist input fails,
`E_CE` is finite and every parameter outside it gives a non-CE twisted group
algebra and hence a countable nonhyperlinear central extension. Moreover
`metaplectic-half-parameter-is-ce` proves `1/2 in E_CE`, so the finite branch
has even order; the first unresolved rational test is at an odd denominator,
not at the metaplectic double cover.
