---
rg: 2
id: iwahori-transfer-reduces-to-square-root-block-mixing
kind: claim
title: Iwahori commutant transfer reduces to positive-density modular square-root mixing
distinct_from:
  iwahori-counterexample-has-exact-first-vertex-blocks: that makes the first vertex an exact direct sum; this identifies the single second-vertex generator that can still cross the two blocks.
---

If `iwahori-unitary-commutant-transfer` fails, then its projection witnesses
may be chosen as in `iwahori-counterexample-has-exact-first-vertex-blocks`
and, after passing to a subsequence, have the following sharper form.  Write

```text
X_n=pi_(n,-)(u),       Y_n=pi_(n,+)(l),               (SRM1)
```

for the two unipotent generators in the standard opposite-Iwahori
coordinates.  Then

```text
[P_n,Y_n]=0,                                           (SRM2)
||[P_n,X_n^2]||_2 -> 0,
||[P_n,pi_(n,-)(l)]||_2 -> 0,                         (SRM3)
liminf ||[P_n,X_n]||_2 > 0.                           (SRM4)
```

Both blocks of `P_n` have normalized dimension bounded below.  Thus every
failure is concentrated in a positive-density choice of square root: the
second unipotent `X_n` mixes the two blocks although its square, the opposite
unipotent, and the entire first modular vertex preserve them asymptotically.

Equivalently, in the associated tracial matrix ultraproduct there are exact
unitaries `X,Y` and a nontrivial projection `P` such that

```text
(X^2,Y) and (X,Y^2) are exact SL_2(Z) representations, (SRM5)
Z(X^2,Y)=Z(X,Y^2),                                    (SRM6)
[P,X^2]=[P,Y]=0, but [P,X]!=0.                         (SRM7)
```

If `V=2P-1`, then `X'=VXV` is a second square root of `X^2`, and
`(X',Y^2)` is another exact modular representation.  It differs from
`(X,Y^2)` precisely by the surviving positive-density off-diagonal branch.
Consequently the open transfer theorem is no longer a general almost-
intertwiner problem: it is the exclusion of this modular square-root branch
mixing.
