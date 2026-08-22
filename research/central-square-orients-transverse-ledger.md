---
rg: 2
id: central-square-orients-transverse-ledger
kind: claim
title: A central square clause orients the transverse ledger without adjoining the branch flip
distinct_from:
  projective-atlas-cannot-orient-transverse-branch-phase: that proves PGL data are phase blind; this gives the minimal phase-sensitive lift once a raw unitary representative is exposed.
  branch-flip-pauli-extraction-cancels-schur-surplus: that adjoins an off-diagonal flip and generates the full branch M2; this clause lies in the multiplicity algebra and does not enlarge the branch packet.
  bcs-projective-kernel-phase-compilation: that seeks a nonlinear predicate phase with a matrix gap; this is a local exact orientation clause conditional on one named Schur holonomy lift.
---

# A central square clause orients the transverse ledger without adjoining the branch flip

ESTABLISHED. Let `W` be a **named unitary lift** of the projective Schur
holonomy, and let `J` be a central involution commuting with `W`. The ordinary
group relation

```text
W^2=J                                                    (CSO1)
```

is odd under the invisible Atlas phase rotation: `(iW)^2=-W^2`. Unlike the
branch flip, `W^2` acts wholly in the multiplicity algebra. Adjoining `(CSO1)`
does not add an off-diagonal operator between the two Schur child lines and
therefore does not generate their full `M_2` algebra.

Decompose into the central sign sectors `J=epsilon I`, `epsilon in {+1,-1}`.
For the real/skew parts

```text
S=(W+W^*)/2,       T=(W-W^*)/2,
C_S=SU,            C_T=TU,                               (CSO2)
```

the clause gives an exact oriented dichotomy:

```text
J=+1:  W=W^*,   T=0,   C_T=0,   C_S is unitary;
J=-1:  W=-W^*,  S=0,   C_S=0,   C_T is unitary.          (CSO3)
```

Thus the payload central sign chooses one retained return and makes the other
a full paid exit. The `M_T direct_sum M_S` selector escape is impossible at
fixed `J`: rotating one summand by `i` reverses `W^2` and hence also reverses
the represented value of `J`.

The orientation is quantitatively robust with sharp constants. On the
`J=+1` sector,

```text
||W-W^*||_2=||W^2-I||_2,
||T||_2=1/2 ||W^2-I||_2;                                 (CSO4)
```

on `J=-1`,

```text
||W+W^*||_2=||W^2+I||_2,
||S||_2=1/2 ||W^2+I||_2.                                 (CSO5)
```

Since `S,T` are contractions, the active-return unitarity deficit has
normalized HS norm at most half the clause defect, while the exit-return
amplitude has HS norm at most half that defect. Hence `(CSO1)` converts the
aggregate identity `D_T+D_S=I` into a one-sided branch ledger without a
dimension-dependent loss.

There is no algebraic completeness obstruction: the cyclic packet
`<W,J | J^2=1, W^2=J>` has exact models with `J` nontrivial. The remaining
problem is not representation theory but incidence. The binary Schur/Atlas
construction currently exposes only `[W] in PGL`, not a raw group word whose
restriction to the same payload corner is `W`. One must construct that lift
and impose `(CSO1)` without making it act on unrelated sectors or collapsing
the payload central sign. Conditional on such a raw-lift compiler, the local
selector-pinning and branch-payment problem is solved exactly.

The obvious reverse-edge compiler is excluded by
`two-chart-square-lift-recreates-schur-m2`: a stable letter crossing the two
Schur children does make its two-edge loop a raw holonomy, but the letter
itself supplies matrix units between the child projections and consumes the
factor-two surplus. An auxiliary chart swap avoids that cancellation only by
ceasing to represent the child-relative holonomy.
