---
rg: 2
id: aggregate-cross-commutator-sum-has-finite-s6-gauge
kind: claim
title: The aggregate cross commutator forms completeness internally but retains a finite S6 gauge
artifacts:
  - research/aggregate-cross-commutator-sum-proof.md
distinct_from:
  signed-hecke-normalizer-has-eight-external-root-returns: that writes a constant external root as one inverse-pair commutator using `t_0s_0=1`; this forms `q_0+q_1=1` inside one aggregate row-column commutator built from both cross matrix units.
  stabilized-cross-braid-has-s3-square-gauge-fence: that separates the complementary packets into two private three-coordinate braids before fusion; this places both complementary products in one literal four-coordinate commutator occurrence.
  asymmetric-depth-two-fold-return-retains-external-gauge: that additively folds three prefix projections in one root subgroup; this obtains the constant coefficient as the noncommutative sum `pr+rp` in one mixed root-channel cell.
---

**ESTABLISHED AGGREGATE-SUM FENCE.**  Use stable coordinates `9,10` and
put

```text
A=x_79(p)x_(7,10)(r),
B=x_98(r)x_(10,8)(p),          p=s_0t_1, r=s_1t_0.    (ACS1)
```

The two factors inside `A` share a row and commute; those inside `B` share
a column and commute.  Writing their nilpotent parts as

```text
X=pE_79+rE_(7,10),       Y=rE_98+pE_(10,8),           (ACS2)
```

gives

```text
X^2=Y^2=YX=0,
XY=(pr+rp)E_78=(q_0+q_1)E_78=E_78.                  (ACS3)
```

Therefore the literal ordinary Steinberg word satisfies

```text
[A,B]=x_78(pr+rp)=x_78(1)=:N.                        (ACS4)
```

This is the first natural coefficient-sum cell in this search where
completeness is formed inside one aggregate commutator rather than after two
output roots or two private Whiteheads have already separated.  It is a
genuine external signed-Hecke return.

It still does not authenticate an ungauged selector.  The aggregate actors
`A,B` are involutions, so their reservoir factors may be involutions
`alpha,beta`, while `(ACS4)` imposes only

```text
E=[alpha,beta]=(alpha beta)^2.                         (ACS5)
```

There is an exact finite model retaining the native order-three holonomy.
In `S_6`, take

```text
alpha=(2 4)(5 6),       beta=(1 4)(2 3),
E=(1 3)(2 4),           D=(1 3)(2 5).                (ACS6)
```

Then

```text
alpha beta=(1 2 3 4)(5 6),
[alpha,beta]=(alpha beta)^2=E,
DE=(2 4 5).                                             (ACS7)
```

Thus every displayed aggregate relation is exact while the native gauge
`D` and external-return gauge `E` still have product of order three.  If the
four private root factors in `(ACS1)` are also named, a scoped extension is
obtained by assigning the active factor of each aggregate to one private
name and the complementary spectator name to the identity; the row/column
commutations and `(ACS4)` remain exact.  Hence the aggregate relation alone
does not force both private reservoir factors to be active or identified.

Appending the return to the cross Whitehead gives only

```text
(NK_0)K_0=N,                                           (ACS8)
```

which is normalizer dressing of the already exposed `K_0` occurrence.  No
new ordinary identity equates the multiplicity factor of `A` or `B` with
the native Whitehead factor `D`; `(ACS5)` merely reconstructs the old
external factor `E`.

Therefore even a literal internal completeness sum does not close ESB.  A
positive cell must share an actual private root occurrence with the native
`J_i`/Singer word or add a further same-carrier relation involving `D` and
one of `alpha,beta`; an aggregate commutator returning the known external
root remains gauged.

No Property T, Kazhdan input, trace hypothesis, literature theorem, local
computation, or Lean compilation is used.

DERIVATION
aggregate-cross-commutator-sum-proof
