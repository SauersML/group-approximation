---
rg: 2
id: atlas-19243-s3-relative-normal-form
kind: claim
title: Collision 19243 is an S3-relative one-involution equation with an exact S4 regular-margin model
distinct_from:
  atlas-word-19243-is-kernel-relation: that proves the word dies in the Leavitt group; this identifies its exact relative-chart normal form and proves the word alone still has a finite regular-margin realization.
  atlas-two-s3-covariance-collapse: that asks the full atlas packet to collapse two named covariance directions; this shows the first interior separator alone cannot do that, even at exact defect zero.
artifacts:
  - experiments/atlas-word-19243.json
  - experiments/atlas_19243_s3_relative.py
---

**ESTABLISHED.**  Absorb the fixed classical chart alignment and let `U` be
the remaining relative unitary between the two regular `A_8` charts.  In the
stored eight-syllable collision word `q_19243`, all four first-chart syllables
are the same nontrivial involution `b`, while the four aligned second-chart
syllables are

```text
r, s, r^2, s r,
```

where

```text
r^3=s^2=1,     s r s=r^-1.
```

Thus `<r,s> ~= S_3`.  Put

```text
c=U^* rho(b) U.
```

Conjugating the whole evaluated word by `U^*` gives the exact equivalence

```text
q_19243(U)=1
  <=>
r c s c r^-1 c (s r) c=1.                         (S3-19243)
```

The reduced equation has an exact finite solution already in `S_4`:

```text
r=(1 2 3),
s=(1 2),
c=(1 3)(2 4).
```

These permutations satisfy `(S3-19243)` and generate all of `S_4`.

Moreover this lifts to the literal regular-`A_8` chart margin.  The restriction
of `Reg(A_8)` to `<r,s> ~= S_3` is

```text
3360 * Reg(S_3),
```

while

```text
840 * Reg(S_4) |_S3 = 3360 * Reg(S_3).
```

Choose a unitary identifying these `S_3`-representations and transport the
`S_4` involution `c` to the `20160`-dimensional regular `A_8` space.  It has
trace zero and hence equal `+1/-1` multiplicities, exactly as the regular
matrix of the nontrivial involution `b`.  Therefore it is unitarily conjugate
to `rho(b)`, so it is `U^*rho(b)U` for some relative chart unitary `U`.
For that `U`, collision `19243` vanishes **exactly**, while both chart
restrictions retain the regular `A_8` character.

Consequently collision `19243` cannot by itself yield any matricial gap,
operator-scaling deficit, or regular-margin nonhyperlinearity obstruction.
Its role must be genuinely relative to additional boundary/full-atlas
relations.  The useful reduction is that every such combined attack may treat
the interior part as the single `S_3`-relative involution equation
`(S3-19243)` rather than as an opaque eight-syllable atlas word.
