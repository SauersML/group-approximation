---
rg: 2
id: qutrit-head-exactification-halves-every-carrier
kind: claim
title: Exact head survival halves every qutrit carrier and exposes a one-branch gap
artifacts:
  - research/qutrit-head-exactification-carrier-proof.md
distinct_from:
  qutrit-head-only-overlap-envelope-is-finite: that identifies the scalar-plus-head coefficient envelope as a finite direct product; this exactifies its canonical microstate profile and computes the joint head/qutrit carrier masses.
  qutrit-scalar-exactification-has-no-central-index: that closes bare conjugacy and central extensions after exactifying only K; this treats the noncentral head involution, whose canonical negative cut has weight one half.
  weighted-unitary-hall-deficit-gap: that is the general weighted terminal; this supplies the exact qutrit weights and a compatible free-product counterprofile showing which missing incidence must authenticate the terminal.
---

Put

```text
K=GL_28(F_2),       A_Q=F_2[Q],       Q^2=Q,
B=EL_28(A_Q)=K x K.
```

Embed the constant copy of `K` diagonally and let
`h=x_12(Q)`. Then `B=<K,h>`. In every trace-preserving
hyperlinear microstate sequence for a group containing `B`, joint
finite-group exactification gives exact copies of `B` with regular type
proportions. For the negative head cut

```text
E=(1-h)/2
```

and each qutrit projection `p` in the diagonal copy of `C[K]`,

```text
||E p||_2^2 -> tau_K(p)/2.                              (QHE1)
```

In particular,

```text
||E q||_2^2       -> 1/6,
||E R||_2^2       -> 1/9,
||E(q-R)||_2^2    -> 1/18.                              (QHE2)
```

Thus the head-surviving sector is positive and cannot be replaced by the
head-killing retraction sector in canonical microstates.

Let `U_l` be an actor unitary, and transport `E,q,R` by conjugacy.
If a fixed mixed occurrence forces the transported head-`R` carrier to
factor, up to `o(1)` in normalized Hilbert--Schmidt norm, through one
transported head-`(q-R)` carrier by contractions, then

```text
liminf ||source-target||_2
 >= 1/3-1/(3 sqrt(2))
 = (sqrt(2)-1)/(3 sqrt(2)) > 0.                         (QHE3)
```

That occurrence would be a terminal contradiction. Two orthogonal
head-`(q-R)` branches have exactly the same total squared mass as one
head-`R` branch, so the three-phase packet does not create a deficit
unless the raw `S/T` relation authentically removes or identifies a
branch.

This restriction is real. The free product

```text
B * Z
```

is residually finite and has canonical trace-preserving finite models in
which the qutrit cell, the nonzero head cut, an infinite actor, and every
bare conjugacy transport coexist. Therefore finite-head exactification plus
abstract actor transport cannot prove nonhyperlinearity. The exact next
object is a typed compression of the alternating `TS=1` closure relation:
retain the separate opposite root and prove that its raw `SQ/T` polar
return factors the head-`R` occurrence through only one complement
branch. Without that carrier statement, the balanced Jacobson host remains
a plausible hyperlinear candidate.
