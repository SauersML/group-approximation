---
rg: 2
id: soft-cyclic-phases-can-support-all-ir-clauses
kind: claim
title: Collapsing cyclic phase gaps can support IR1, IR2 and a surviving compressed adjoint moment
distinct_from:
  perfect-quotient-ir-survival-requires-nonscalar-mass: that uses perfectness to rule out a purely scalar retained escape for the Leavitt quotient; this gives a nonperfect finite cyclic quotient where that escape is exact.
  hall-reflection-realizes-rank-one-restriction-instability: that has an exact one-dimensional zero mode but its normalized adjoint displacement vanishes; this has an unbounded, quarter-density retained sector with a limiting phase minus one.
  uniformly-discrete-block-monomial-images-are-sofic: that assumes a uniform gap for every nonidentity block label; here the kernel label is nonidentity at every finite stage while its character gap collapses to zero.
  shulman-presentation-double-witnesses-have-adjoint-normal-form: that gives the adjoint normal form and exact commutant equality for the Leavitt presentation double without an IR band; this is a finite-cyclic calibration satisfying those structural conclusions and all three IR clauses.
---

**ESTABLISHED SOFT-PHASE COUNTERMODEL.** There is a fixed presentation

```text
Q=F/K=Z/2,             F=<a>,             K=<a^2>,     (SCP1)
```

and globally conjugate exact representation pairs satisfying the adjoint
normal form, exact commutant equality, and `(IR1)--(IR3)` on retained sectors
whose ranks tend to infinity and occupy one quarter of the ambient
Hilbert--Schmidt dimension.

Choose roots of unity

```text
z_n=-exp(2 pi i/N_n),                 N_n->infinity,   (SCP2)
```

with `z_n^2!=1`, and arbitrary `s_n->infinity`.  On `C^(2s_n)` put

```text
sigma_n(a)=diag(1_(s_n),z_n 1_(s_n)),
V_n=the unitary swapping the two s_n blocks,
v_n=sigma_n,                 u_n=V_n^* sigma_n V_n.    (SCP3)
```

Under `T |-> V_n T`, the left-right representation is `Ad(sigma_n)`.  Let
`W_n` be the upper-right `s_n by s_n` matrix block.  Then

```text
dim W_n=s_n^2=(1/4) dim HS(C^(2s_n)),                  (SCP4)
Ad(sigma_n)(a)|_(W_n)=conjugate(z_n) 1_(W_n).          (SCP5)
```

Thus `W_n` is exactly reducing, every `a^(2l) in K` acts on it by
`conjugate(z_n)^(2l)->1`, while

```text
||(Ad(sigma_n)(a)-1)|_(W_n)||_(2,W_n)
   =|z_n-1| -> 2.                                      (SCP6)
```

So `(IR1)--(IR3)` all hold, and the compressed adjoint moment tends to
`-1`.  At every finite stage

```text
sigma_n(K)'=sigma_n(F)'=M_(s_n) directSum M_(s_n),     (SCP7)
```

because both `z_n` and `z_n^2` differ from one.  The kernel action is
nevertheless soft:

```text
1-Re(z_n^2)->0.                                        (SCP8)
```

All matrices lie in finite-phase monomial groups because every `z_n` is a
root of unity.

Therefore no theorem using only block-monomiality, growing retained rank,
positive ambient density, adjoint normal form, exact commutant equality and
collapsing kernel energy can force `(IR3)` to vanish.  The Leavitt problem
must use quotient-specific structure; `perfect-quotient-ir-survival-requires-nonscalar-mass`
shows that perfectness already excludes this purely scalar calibration but
does not exclude a genuinely nonscalar soft-label sector.

DERIVATION
two-block-soft-phase-ir-calculation
