---
rg: 2
id: congruence-tensor-regularizes-sl3-swap-profile
kind: claim
title: Congruence tensoring makes every SL3 swap model actor-regular and swap-balanced without changing its fold moments
distinct_from:
  regular-actor-balanced-swap-has-positive-second-fold-bias: that is the open scalar terminal; this proves that its trace-profile hypotheses can be imposed on an arbitrary approximate model at zero cost.
  canonical-arithmetic-swap-fold-gram-is-arcsine: that uses the full canonical character of the swap extension; this regularizes only the actor character and swap trace and preserves, rather than determines, all fold moments.
  finite-swap-conjugate-moments-do-not-fold-arithmetic-double: that models a fixed lamp-only moment table after omitting the actor extension; this keeps every approximate actor/swap relation already present and tensors it with an exact congruence representation.
---

**ESTABLISHED PROFILE REGULARIZATION.**  Put

```text
A=SL_3(Z[1/2]),
C=SL_3(Z),
E=<A,s | s^2=1, [s,C]=1>,
h=diag(2,1,1/2).
```

Let `psi_n` be any sequence of finite-dimensional unitary assignments for
a fixed presentation of `E`, with presentation defect tending to zero.
After passing to a subsequence if needed, there are exact finite-dimensional
representations `theta_n:E->U(k_n)` such that

```text
tr(theta_n(a))->0             for every 1!=a in A,
tr(theta_n(s))=0,
theta_n(hsh^(-1)s)=I.                                  (CTR1)
```

The tensor assignments

```text
rho_n=psi_n tensor theta_n                              (CTR2)
```

have the same presentation defect as `psi_n`, satisfy the regular-actor and
balanced-swap profile, and preserve every fold moment:

```text
tr(rho_n((hsh^(-1)s)^m))
 =tr(psi_n((hsh^(-1)s)^m))       for every fixed m.     (CTR3)
```

Construction: residual finiteness of the linear group `A` gives finite
quotients `q_n:A->Q_n` which eventually separate every fixed nonidentity
element.  On

```text
ell^2(Q_n) tensor C^2
```

put

```text
theta_n(a)=lambda_(Q_n)(q_n(a)) tensor I_2,
theta_n(s)=I tensor diag(1,-1).                          (CTR4)
```

This is an exact representation of `E`; its swap commutes with all of `A`,
so its fold is one.  The regular finite-quotient trace and the external bit
give `(CTR1)`.  A relator evaluates under `(CTR2)` as its `psi_n` evaluation
tensored with the identity, proving defect preservation, while the fold
evaluation is the old fold tensored with the identity, proving `(CTR3)`.

## Consequence

`regular-actor-balanced-swap-has-positive-second-fold-bias` is equivalent to
the apparently stronger defect-only assertion that there is an
`epsilon_*>0` such that **every** vanishing-defect sequence `psi_n` satisfies

```text
liminf_n Re tr(psi_n((hsh^(-1)s)^2))>=epsilon_*.        (CTR5)
```

One implication is restriction to the regular/balanced profile.  For the
other, apply the tensor regularizer and use `(CTR3)`.  Thus the profile
hypotheses do not create a genuinely smaller model class after amplification.
The terminal remains weaker than fold-square rigidity only in its numerical
conclusion: a fixed positive second moment rather than convergence to one.
