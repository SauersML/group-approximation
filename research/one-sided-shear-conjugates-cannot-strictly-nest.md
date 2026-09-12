---
rg: 2
id: one-sided-shear-conjugates-cannot-strictly-nest
kind: claim
title: A one-orientation shear conjugate of an equal-rank finite-chart idempotent cannot sit strictly below another chart idempotent
invalidates: [leavitt-df-failure-by-single-shear-conjugation]
distinct_from:
  nested-two-finite-subgroup-idempotents-have-strict-rank: that assumes the smaller idempotent is literally supported in a finite subgroup and two-sided nested; this allows a square-zero shear of arbitrary support around it and needs only one-sided nesting.
  subgroup-supported-one-sided-inverse-rigidity: that constrains an intertwiner whose support generates a directly finite subgroup; this constrains the conjugating unit itself, with shear support in the whole group.
---

Let `p` be prime, `G` a group, `S = F_p[G]`, and `K, K' <= G` finite subgroups.
Let `P in F_p[K]` and `f in F_p[K']` be idempotents of equal normalized rank:

```text
dim(P F_p[K]) / |K| = dim(f F_p[K']) / |K'|.
```

Let `N in S` satisfy `N^2 = 0`, and put `D = (1+N) f (1-N)`, an idempotent similar
to `f`.

1. If `P N = 0` and `N P = N`, then `D P = D` implies `P D = P`, so `S D = S P`.
   If moreover `P D = D`, then `D = P`.
2. If `P N = N` and `N P = 0`, then `P D = D` implies `D P = P`, so `D S = P S`.
   If moreover `D P = D`, then `D = P`.

So a single shear from one Peirce corner of `P`, of any support, cannot move an
equal-rank chart idempotent to a proper submodule of `S P` or of `P S`, and a
two-sided strict nesting `D < P` is impossible. A group conjugation
`f -> g f g^-1` is absorbed by replacing `K'` with `g K' g^-1`. Hence every unit of
the form `(1+N)[g]` fails as a Hilbert-hotel compressor between equal-rank chart
projectives. Shears in both orientations are needed. That is what the
half-corner construction uses, and it is the open case.

The only relations used are those of the amalgam `K *_(K cap K') K'`, which is
virtually free and residually finite, so the rank comparison happens in finite
quotients. ESTABLISHED by [[one-sided-shear-nesting-amalgam-proof]].
