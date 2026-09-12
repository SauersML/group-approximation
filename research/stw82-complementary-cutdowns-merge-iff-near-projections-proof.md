---
rg: 2
id: stw82-complementary-cutdowns-merge-iff-near-projections-proof
kind: route
title: Prove the quantitative complementary-cutdown equivalence
target: stw82-complementary-cutdowns-merge-iff-near-projections
requires: []
---

Suppose first that `a,b` are positive contractions, `ab=0`, and both
approximation errors in (1) are at most `delta`.  Then

```text
h(1-h)
 = (h-a)(1-h) + a((1-h)-b) + ab,
```

and contractivity gives (C1).

Now put `eta=norm(h-h^2)`.  The spectral mapping theorem says that every
`t in spectrum(h)` satisfies `t(1-t)<=eta`.  For `eta<1/4`, the spectrum is
contained in

```text
[0,r] union [1-r,1],
r=(1-sqrt(1-4 eta))/2 < 1/2.
```

The characteristic function of the second component is continuous on
`spectrum(h)`.  Hence

```text
p=chi_[1/2,1](h)
```

is a projection in `C*(1,h) subset B`, and the spectral estimate is exactly
`norm(h-p)<=r`, proving (C2).  Taking `a=p` and `b=1-p` proves (2) implies
(1), as well as (2) implies (3).  Finally, if `norm(h-p)<=delta` for a
projection `p`, then

```text
norm(h-h^2)
 <= norm(h-p)+norm(h^2-p^2)
 <= 3 delta,
```

so (3) implies (2).  This proves all equivalences without any commutativity
or near-projection assumption at the outset.
