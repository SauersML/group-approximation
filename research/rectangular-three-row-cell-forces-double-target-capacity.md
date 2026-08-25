---
rg: 2
id: rectangular-three-row-cell-forces-double-target-capacity
kind: claim
title: The three-row Leavitt cell needs only a strict target-capacity deficit
distinct_from:
  two-inverses-one-cross-have-quadratic-hs-floor: that puts all four coefficients in one square corner and obtains a quadratic carrier floor; this permits a rectangular source and target and identifies the sharp capacity threshold two.
  mixed-steinberg-loops-admit-morita-rectangular-model: that gives the exact source-to-doubled-target model; this proves quantitatively that its factor two is the sharp saturation case.
  paired-same-reservoir-boundary-lemma: that asks to identify the identical multiplicity reservoir or pay its boundary through an iterated root chart; this shows that exact identity is stronger than necessary and may be replaced by any fixed deficit below doubled target capacity.
---

**ESTABLISHED.**  Let `(M,tau)` be a finite tracial von Neumann algebra and
let `E,F in M` be projections.  Put

```text
q=tau(E),                 r=tau(F).
```

For contractions

```text
s_i in F M E,             t_i in E M F,       i=0,1,
```

define the two diagonal-return defects and one crossed defect by

```text
epsilon_i=||t_i s_i-E||_2,                 i=0,1,
eta=||t_0s_1||_2.                                      (RTC1)
```

Then

```text
r >= 2q-10 sqrt(q) epsilon_0
          -2 sqrt(q) epsilon_1-4 eta^2.                (RTC2)
```

In particular the exact three-row table

```text
t_0s_0=E,             t_1s_1=E,             t_0s_1=0  (RTC3)
```

forces

```text
tau(F)>=2tau(E).                                       (RTC4)
```

The constant two is sharp: the native rectangular Morita model takes
`F=E direct_sum E`, puts the two `s_i` in the two coordinate inclusions and
the `t_i` in the coordinate projections, and has equality in `(RTC3)--(RTC4)`.

Consequently a full same-object decoder is unnecessary.  Suppose some
matrix-coordinate extraction supplies the rectangular rows `(RTC1)` and a
conditional capacity estimate

```text
r <= (2-kappa)q+zeta,              kappa>0.             (RTC5)
```

Then

```text
kappa q
 <=10 sqrt(q)epsilon_0+2 sqrt(q)epsilon_1
   +4eta^2+zeta.                                        (RTC6)
```

If `epsilon_0,epsilon_1,eta<=delta` and `zeta<=c delta^2`, solving the
quadratic in `sqrt(q)` gives

```text
sqrt(q)
 <=(6+sqrt(36+kappa(4+c)))/kappa * delta,              (RTC7)
```

and hence a dimension-independent quadratic carrier floor.  More generally
`(RTC6)` is the exact error ledger when the capacity row has its own modulus.

This strictly narrows the object-erasing problem.  The outer-root Leavitt
table already has one common source object and one common target object;
its finite rectangular countermodel survives because the target has exactly
twice the source capacity.  A successful payload-coupled word gadget need
not identify those objects.  It is enough to authenticate the three rows on
one source/target pair and force the target used by those same occurrences
to have any fixed conditional trace deficit below `2q`.  Conversely no
argument using only the currently named typed Morita rows can yield such a
deficit, since their exact model saturates `(RTC4)`.

DERIVATION
rectangular-three-row-capacity-proof
