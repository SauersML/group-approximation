---
rg: 2
id: problem141-common-kernel-double-contains-product-proof
kind: route
title: The user-supplied difference element centralizes the normal kernel, has reduced powers, and lies in the fold kernel
target: problem141-common-kernel-double-contains-product
requires: []
artifacts:
  - research/artifacts/problem141-user-document-integration-2026-09-20.md
---

This is the user's elementary argument from the supplied Problem 141
proof attempt, with every hypothesis retained.

By the amalgam normal-form theorem, the vertex maps `j_1,j_2` are
injective and identify their copies of `Lambda`. In particular they
identify their copies of `N`; write this common subgroup simply as `N`.
Choose `t in P minus Lambda` and put `s=j_2(t)^(-1)j_1(t)`.

For `n in N`, normality in `P` gives `tnt^(-1) in N <= Lambda`.
Consequently

```
s j_1(n) s^(-1)
 = j_2(t)^(-1) j_1(tnt^(-1)) j_2(t)
 = j_2(t)^(-1) j_2(tnt^(-1)) j_2(t)
 = j_2(n)
 = j_1(n).
```

Thus `s` centralizes `N`. For every positive integer `m`, the word
`(j_2(t)^(-1)j_1(t))^m` alternates between the two vertex groups,
with all `2m` syllables outside the edge subgroup: both `t` and
`t^(-1)` lie outside `Lambda`. It is a reduced amalgam word and is
nontrivial. This proves that `s` has infinite order.

The fold homomorphism `r:D->P`, identical on each vertex copy, exists
by the amalgam universal property. It satisfies `r(s)=1` and restricts
to the identity on `N`. Hence `N intersect <s>=1`: an element in this
intersection maps both to itself and to the identity under `r`.

Since the subgroups commute, `(n,m)->j_1(n)s^m` is a homomorphism
from `N x Z`. If its value is the identity, applying `r` gives `n=1`,
and the infinite order of `s` then gives `m=0`. This proves injectivity.

If `n_0 in N` has infinite order, the restriction to
`<n_0> x <s>` embeds `Z^2`. A word-hyperbolic group contains no
`Z^2` (equivalently, its abelian subgroups are virtually cyclic),
so this double is not word-hyperbolic. No conclusion here assumes
that an arbitrary infinite `N` contains an infinite-order element.
