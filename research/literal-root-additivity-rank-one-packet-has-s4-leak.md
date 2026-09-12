---
rg: 2
id: literal-root-additivity-rank-one-packet-has-s4-leak
kind: claim
title: The literal two-root rank-one denominator packet has an exact S4 leak
distinct_from:
  root-additivity-eliminates-the-s3-rank-one-leak: that excludes the packet only in S3; this supplies the next finite enemy and disproves the corresponding dimension-free implication.
  rank-one-self-commutator-coboundary-packet-has-s3-leak: that makes the three lattice words independent; this retains their literal construction from the same two root variables.
  one-root-p3-denominator-fragment-has-finite-regular-leaks: that keeps a root-scaling fragment but omits the rank-one Weyl decomposition; this satisfies the literal two-root denominator identity exactly.
---

The literal root-additive strengthening of the rank-one denominator packet
does not force projective transfer in arbitrary finite-dimensional models.
There are elements `u,h,a,b in S_4` satisfying

```text
[u,a]=[u,b]=1,                                           (RAS4-1)
h=a^2 (h b^(-2) h^(-1)) a b a^(-1),                    (RAS4-2)
[u,h] != 1.                                              (RAS4-3)
```

Explicitly, in cycle notation take

```text
a=u=(2 3 4),       b=(2 4 3)=a^(-1),
h=(1 2)(3 4).                                           (RAS4-4)
```

Under the substitutions

```text
X=a^2,       Y=b^(-2),       C=a^(-1)b a^(-1),          (RAS4-5)
```

equation `(RAS4-2)` is exactly the literal rank-one decomposition
`H=X(HYH^(-1))XC`. Thus the model retains the common two-root origin of
`X,Y,C`, not merely the five independent variables of the earlier `S_3`
countermodel.

In the 24-dimensional left regular representation of `S_4`, all these
relations hold exactly and the nonidentity marked word `[u,h]` has normalized
trace zero. Consequently no dimension-free projective-transfer estimate can
follow from root additivity and the rank-one denominator identity alone, even
at zero defect.

This is a counter-fence, not progress toward the relative-commutant collapse.
The next viable arithmetic packet must use data absent here, such as a
rank-two shared-root Steinberg relation on the same carrier; merely enlarging
the finite group while retaining only `(RAS4-1)--(RAS4-2)` cannot prove the
needed transfer.
