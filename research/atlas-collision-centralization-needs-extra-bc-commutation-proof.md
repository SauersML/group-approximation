---
rg: 2
id: atlas-collision-centralization-needs-extra-bc-commutation-proof
kind: route
title: Tietze-reduce collision and audit the provenance of its commutation premise
target: atlas-collision-centralization-needs-extra-bc-commutation
requires:
  - atlas-forward-collision-bass-serre-reduction
  - atlas-14-core-q19243-gl5-countermodel
---

Use

```text
y=t^-1,       b=s t,       s=b y,
y^3=b^2=c^2=1,             b y b=y^-1.             (TC-1)
```

Temporarily impose `[b,c]=1` and put `a=bc`; then `a^2=1`.  Starting from the
literal collision word gives

```text
q=t c s c t^-1 c s t c
 =y^-1 c b y c y c b c
 =y^-1 a y b a y b
 =y^-1(a y b)^2.                                    (TC-2)
```

Thus `q=1` says `x^2=y` for `x=a y b`.  Conversely

```text
a=x b y^-1=x b x^-2.
```

Using `a^2=1`,

```text
1=x b x^-1 b x^-2,
b x^-1 b=x,
b x b=x^-1.                                         (TC-3)
```

Since `y^3=x^6=1`, equations `(TC-3)` give

```text
a=x^3 b,       c=b a=b x^3 b=x^-3=x^3,
[c,x]=[c,y]=[c,b]=1.                                (TC-4)
```

Every step is a Tietze substitution or multiplication by a displayed
relator.  The premise audit is equally exact: in
`atlas-forward-collision-bass-serre-reduction`, `c` lies in the vertex `F`,
`b` lies in `C` and `K`, and the amalgamated subgroups are only
`A=<r,z>` and `B=<b>`.  Hence `[b,c]` is absent.  It appears in the structural
finite carrier because that carrier deliberately aligns the marked overlap as
an elementary abelian 2-subgroup.

Finally, `atlas-14-core-q19243-gl5-countermodel` is an exact representation of
all fourteen core relators and `q=1` with the marked collision coefficient
nontrivial.  It rules out any derivation of `c=1` from the literal fourteen
core words plus collision, independently of presentation manipulations.
