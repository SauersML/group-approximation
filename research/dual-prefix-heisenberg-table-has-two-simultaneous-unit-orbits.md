---
rg: 2
id: dual-prefix-heisenberg-table-has-two-simultaneous-unit-orbits
kind: claim
title: Every dual-prefix Heisenberg pair is simultaneously equivalent to one of two prototypes
distinct_from:
  leavitt-prefixes-form-exponential-heisenberg-packet: that computes the diagonal pairing by cancelling prefixes; this compresses all diagonal and off-diagonal coefficient pairs to two simultaneous unit orbits.
  binary-leavitt-bounded-area-chromatic-code: that asks for uniformly bounded presentation fillings of the infinite commutator table; this proves the underlying stabilized algebraic two-orbit statement and isolates the remaining word-coherence cost.
  orthogonal-idempotent-sum-has-a-stabilized-steinberg-conjugacy: that conjugates an orthogonal block sum to one stabilized corner; this simultaneously conjugates a composable row/column pair while preserving whether its product is one or zero.
artifacts:
  - research/property-t-free-leavitt-full-mf-radical.md
---

**ESTABLISHED.**  Let `R=L_(F_2)(1,2)`.  For binary words `alpha,beta`
of one common positive length, there is a Thompson prefix-code unit
`u_(alpha,beta) in R^x` such that

```text
t_0 u_(alpha,beta)=t_alpha,
u_(alpha,beta) s_beta=s_epsilon,                         (DPU1)
```

where `epsilon=0` if `alpha=beta` and `epsilon=1` otherwise.  Consequently

```text
t_alpha u_(alpha,beta)^(-1)=t_0,
u_(alpha,beta)s_beta=s_epsilon.                         (DPU2)
```

Put `D_(alpha,beta)=diag(1,u_(alpha,beta),1)`.  Conjugation in
`GL_3(R)` gives simultaneously

```text
D x_12(t_alpha) D^(-1)=x_12(t_0),
D x_23(s_beta)  D^(-1)=x_23(s_epsilon).                 (DPU3)
```

Thus every diagonal entry of the depth-`n` Heisenberg commutator table is
stably conjugate to the single prototype

```text
[x_12(t_0),x_23(s_0)]=x_13(1),
```

and every off-diagonal entry is stably conjugate to

```text
[x_12(t_0),x_23(s_1)]=1.                               (DPU4)
```

Since `GL_m(R)=EL_m(R)` for `m>=2`, the diagonal unit has an elementary
lift after the fixed stabilization used by the rank-twenty Steinberg target;
central ambiguity in a Steinberg lift does not affect conjugation.  Hence
`(DPU3)` is also an exact simultaneous conjugacy statement in the stabilized
Steinberg group.

This removes coefficient cancellation depth from the **algebraic orbit
classification**, but it does not yet prove bounded relator area in a fixed
finite presentation.  The conjugator depends on the ordered pair
`(alpha,beta)`, whereas the chromatic compactness theorem requires vertex
words `c_alpha` and `h_beta` chosen once.  Rewriting those fixed words into
the pair-dependent chart may still have unbounded filling area.  The precise
remaining gate is therefore a coherent two-orbit wordization, not another
Leavitt coefficient identity.

