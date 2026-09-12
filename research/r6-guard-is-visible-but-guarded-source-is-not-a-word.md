---
rg: 2
id: r6-guard-is-visible-but-guarded-source-is-not-a-word
kind: claim
title: The R6 guard is word-visible but its guarded common-source overlap is not
distinct_from:
  msz-guarded-projection-recurrence-is-relation-r6: that identifies the exact star-polynomial relation and its guard from the sources; this separates the literal guard projection from the nonlinear source moment needed by an ordinary-word D16 charge.
  fanizza-reflection-recurrence-has-s4-stationary-overlap: that gives the unguarded S4 stationary model; this adjoins an independent active/inactive guard, computes the guarded overlap trace, and tests one finite packet extension.
  fanizza-verifier-d16-charger-globalizes-ground-support: that shows the aggregate verifier reflection reads Hamiltonian energy but lacks localized support; this tests whether the native R6 guard supplies that support.
---

# The R6 guard is word-visible but its guarded common-source overlap is not

ESTABLISHED.  Put

```text
gamma=J X_tilde Z_tilde X_tilde Z_tilde,
G=(1+gamma)/2.                                           (RGS1)
```

On the commuting C18 table, R6 is exactly

```text
(P+S-T)G=0,
S=X_tilde P X_tilde,
T=U P U^*.                                               (RGS2)
```

Thus `G` itself is a rational projection of one literal group word.  It is
the active preterminal guard and it vanishes on the marked terminal block.
This does not provide the common-source word needed by the D16 cell.  The
missing positive moment is

```text
G P S.                                                    (RGS3)
```

Indeed, after retaining only the ordinary reflection skeleton

```text
Z=1-2P,       Y=1-2S,       Z'=1-2T,       Z'=ZY,       (RGS4)
```

the reflection which charges `(RGS3)` would be

```text
D=1-2GPS.                                                 (RGS5)
```

There is no word in the three commuting involutions `gamma,Z,Y` equal to
`D` in a representation containing all eight joint characters.  Its truth
table is `+1` at seven characters and `-1` only at

```text
gamma=+1,       Z=-1,       Y=-1,                       (RGS6)
```

whereas every group word is a character
`gamma^a Z^b Y^c`.  This is the three-bit version of the controlled-corner
word barrier.

The obstruction has a finite exact stationary model.  Let

```text
K=C_2(gamma) times S_4,
V=<d,e>=(C_2)^2 < S_4,
P=(1-d)/2,       S=(1-e)/2,       T=(1-de)/2.           (RGS7)
```

In the regular representation of `K`, `(RGS4)` holds exactly and all eight
characters of `<gamma,d,e>` occur.  Moreover

```text
tau(GPS)=1/8.                                             (RGS8)
```

The coefficient calculation is immediate from
`GPS=(1+gamma)(1-d)(1-e)/8`: only the identity term has nonzero regular
trace.  Tensoring this model with any fixed D16 packet preserves `(RGS8)`
and every packet relation.  Hence a finite packet extension which merely
names `G`, supplies the Hadamard selector, and retains the multiplicative
recurrence admits an exact wrong-sector model with positive guarded source
overlap.

This does not contradict the star-algebra R6 relation: `(RGS2)` itself kills
`GPS` on the active guard.  Rather, it proves the precise compiler gap.
R6 offers a word-visible **selector**, but converting its additive content
to ordinary group relations still requires wordizing the guarded AND
`GPS`.  The D16 charger can pay that moment only after a selector-central
return with block `(RGS5)` has already been manufactured, which is exactly
the missing common-source Gram word rather than a consequence of the guard.

