---
rg: 2
id: multiscale-square-function-checksum-forces-hs-floor
kind: claim
title: One multiscale square-function checksum turns recursive error spread into an HS floor
distinct_from:
  contractive-computation-ladder: that bounds every level error separately by a polynomial times one global defect; this permits arbitrarily large rare scale errors and asks only that one checksum control their weighted L2 square function.
  branching-plus-first-hit-exits-forces-hs-floor: that uses an unweighted finite first-hit reservoir; this uses a geometric backward recurrence and an infinite orthogonal scale decomposition of one fixed checksum word.
  bounded-hs-loss-kills-static-heavy-tail-library: that rules out a static density allocation; this records the additional feedback identity which makes a heavy-tailed multiscale construction viable.
---

Let `0<lambda<1`, let `a_n in [0,1]`, and let `s_n>=0`.  Suppose

```text
a_n<=lambda a_(n+1)+C s_n             for every n,    (MSC1)
```

and one global energy `E` controls the weighted square function

```text
sum_(n>=0) lambda^n s_n^2<=K E.                       (MSC2)
```

Then

```text
a_0<=C sqrt(K E/(1-lambda)).                          (MSC3)
```

Consequently a marked floor `a_0>=beta>0` forces

```text
E>=beta^2(1-lambda)/(C^2 K)>0.                        (MSC4)
```

This is a rigorous version of the self-hash/error-spread idea.  Individual
levels may have wild errors and no pointwise estimate `s_n<=p(n)sqrt(E)` is
needed.  The checksum sees their orthogonal L2 square function, while the
recurrence prevents a finite model from moving the first failure to a deep,
low-weight scale without exponentially attenuating the root signal as well.

The natural operator realization is especially small.  If a single fixed
relator defect `D=r(U)-I` has mutually orthogonal decoded scale domains
`P_n` and

```text
s_n=||D P_n||_2,
```

then

```text
sum_n s_n^2<=||D||_2^2.                               (MSC5)
```

Thus `(MSC2)` holds with `K=1` even without the geometric weights.  The
remaining group-theoretic task is not to name infinitely many relators.  It
is to make one finite word carry the orthogonal scale syndromes and make the
same decoded carriers satisfy `(MSC1)` only in finite matrices.

