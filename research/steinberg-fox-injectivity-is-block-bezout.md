---
rg: 2
id: steinberg-fox-injectivity-is-block-bezout
kind: claim
title: Steinberg Fox injectivity is exactly a Bezout identity in the defect-zero block
artifacts:
  - research/steinberg-block-bezout-equivalence-proof.md
distinct_from:
  authenticated-mixed-loop-kills-minuscule-affine-modules: that treats selected defining-characteristic module families and explicitly leaves a universal group-algebra Bezout identity open; this is the exact finite Steinberg block only.
  symmetric-power-fox-kernel-is-smith-obstruction: that is an integral Smith-normal-form obstruction on symmetric powers, while this is a matrix-block left-ideal criterion over F_p.
---

**ESTABLISHED EQUIVALENCE.**  For odd `p`, let

```text
A_p=F_p[SL_3(F_p)]/Ann(St_p)=End_(F_p)(St_p),
```

and let `x,y` be the images in `A_p` of the two Fox rows `X,Y` from
`(SFI2)`.  Then the following are equivalent:

```text
ker(x) intersect ker(y)=0;
v |-> (xv,yv) has a left inverse;
A_p x + A_p y = A_p;
1 = a x + b y for some a,b in A_p.                    (SBB1)
```

By `(SFI4)`, these are also equivalent to injectivity of `D_p`.  This is a
certificate reformulation, not an assertion that the unit-ideal condition
has been proved uniformly in `p`.

DERIVATION
steinberg-block-bezout-equivalence-proof
