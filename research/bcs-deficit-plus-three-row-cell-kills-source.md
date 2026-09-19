---
rg: 2
id: bcs-deficit-plus-three-row-cell-kills-source
kind: claim
title: A shared BCS gap turns a doubled rectangular target into a strict Leavitt capacity deficit
distinct_from:
  rectangular-three-row-cell-forces-double-target-capacity: that supplies the lower bound on a rectangular target from two inverse rows and one crossed-zero row; this uses the nonlinear BCS gap to supply the matching strict upper bound.
  maximal-forbidden-atom-has-a-named-positive-half: that selects one positive forbidden atom on a BCS carrier; this removes that atom from a doubled Leavitt target and combines the resulting deficit with the three-row lower bound.
  capacity-gated-common-corner-bcs-two-cell: that uses common-source context intertwiners to localize the full BCS energy; this assumes a BCS tuple is already decoded on the doubled target and isolates only the final maximal-atom-avoidance incidence.
---

**ESTABLISHED CONDITIONAL COMPOSITION.**  Fix a finite shared BCS with `M`
forbidden types and robust finite-matrix constant `beta>0`.  Work in one
matrix algebra with projections `E,T`, put

```text
q=tr(E),                    h=tr(T),
```

and suppose the decoded BCS tuple reduces `T`.  Let its total forbidden mass
and structural energy obey

```text
V_T>=beta h-C_B sqrt(E_B).                              (BDT1)
```

Choose a forbidden atom `A<=T` of maximal trace.  Then

```text
tr(A)>=(beta/M)h-(C_B/M)sqrt(E_B).                     (BDT2)
```

Put `F=T-A` and suppose the target is at most a doubled source up to `xi`:

```text
h<=2q+xi.                                               (BDT3)
```

If contractions

```text
s_i in F M_d E,             t_i in E M_d F,    i=0,1,
```

have defects

```text
epsilon_i=||t_i s_i-E||_2,       eta=||t_0s_1||_2,    (BDT4)
```

then, with `theta=beta/M`,

```text
2 theta q
 <=10 sqrt(q)epsilon_0+2 sqrt(q)epsilon_1+4eta^2
   +(1-theta)xi+(C_B/M)sqrt(E_B).                      (BDT5)
```

In particular, if the source has fixed positive canonical trace and all
displayed defects tend to zero, no such finite-matrix sequence exists.

## Proof

Maximality and `(BDT1)` give `(BDT2)`.  Since `A<=T`,

```text
tr(F)=h-tr(A)
 <=(1-theta)h+(C_B/M)sqrt(E_B)
 <=(2-2theta)q+(1-theta)xi+(C_B/M)sqrt(E_B).           (BDT6)
```

On the other hand,
`rectangular-three-row-cell-forces-double-target-capacity` applied to the
same `E,F,s_i,t_i` gives

```text
tr(F)>=2q-10sqrt(q)epsilon_0
            -2sqrt(q)epsilon_1-4eta^2.                (BDT7)
```

Combining `(BDT6)` and `(BDT7)` is exactly `(BDT5)`.

## Exact-model compatibility

This composition does not impose a universal finite-tracial contradiction.
In a perfect tracial BCS model every forbidden atom is zero.  Take a
rectangular Leavitt cell with target `T=E direct_sum E`; then `A=0`, `F=T`,
and the two inverse rows and crossed-zero row hold exactly.  Thus the
infinite completeness model sits at the sharp equality

```text
tr(F)=tr(T)=2tr(E).                                    (BDT8)
```

The finite-matrix contradiction enters only through `(BDT1)`.

## Remaining group compiler

The unresolved groupification datum is now one incidence, not a complete
same-reservoir decoder.  From a fixed finite menu, select the maximal
forbidden Reynolds atom `A` and make the three coefficient occurrences act
through its complement `F=T-A`, with `(BDT3)--(BDT4)` controlled by ordinary
presentation defects.  The selection itself is already supplied by
`maximal-forbidden-atom-has-a-named-positive-half`; the missing operation is
the **maximal-atom-avoiding rectangular target row**.  It must be genuinely
matrix-only, since in the group regular trace the named forbidden Reynolds
atoms have positive canonical mass.

DERIVATION
bcs-three-row-capacity-composition-proof
