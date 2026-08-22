---
rg: 2
id: leavitt-d4-l14-fifteen-i4115-fence-proof
kind: route
title: Exhaust both inverse fifteen-winner 4;115 boundaries
target: leavitt-d4-l14-fifteen-i4115-is-fenced
requires:
  - leavitt-d4-l14-fifteen-i4115-carriers-are-explicit
  - maximal-noncrossing-forest-criterion
---

For each of the two exact common-carrier branches, enumerate every
coarsening-maximal forest of the remaining two carriers.  Each branch has
sixteen joint coordinate states.  For each state, take every normalized
cyclic boundary cut, append the once-occurring formal target `Q^-1` in each
copy, eliminate `Q` first, and apply the all-maximal forest/Tietze semiring.

MSI array `16683118` returned the identical result in both branches:

```text
carrier states       16
augmented words       4
boundary states      20
q nonempty            4
q free                0
direct kills          0
power kills           4
unresolved            0
```

In all four terminal states `q=x5`, while the residual presentation contains
both `x5^2` and `x5^3` (along with redundant higher powers).  Hence `x5=1` by
the coprime-power identity, so every apparent target is trivial.
