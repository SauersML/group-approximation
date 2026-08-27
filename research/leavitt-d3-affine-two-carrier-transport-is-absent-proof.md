---
rg: 2
id: leavitt-d3-affine-two-carrier-transport-is-absent-proof
kind: route
title: Recognize common-conjugator transport after exact unary substitution
target: leavitt-d3-affine-two-carrier-transport-is-absent
requires:
  - leavitt-omega-has-an-explicit-distorted-target
  - leavitt-transport-drift-and-l7-atomic-no-go
---

The topology screen enumerates all `C(13,5)=1,287` exponent-three sign paths.
Exactly 260 have stable-letter valences `(1,5,7)` up to orbit order when every
coefficient slot is nonidentity.  For each path, choose four cyclic sign
changes for the ordered gates `(a,b,c,d)` and use two formal carriers on the
other nine slots.

The carrier coloring is any of the 32 nonredundant linear Boolean functions
of five local path features:

```text
index mod 2, current sign, preceding sign,
height mod 3 = 1, height mod 3 = 2.
```

The omitted affine constant merely exchanges `x` and `y`.  Reduction takes
place in the finer free product of the formal cyclic letter groups in the
three coefficient copies.  Therefore an equality found by the screen would
remain an equality after specializing `x,y` to arbitrary compound Leavitt
coefficient words.

For every layout the artifact solves the unique unary relator for `z=t^3`,
substitutes it with the correct signs and order in the two residual relators,
and first applies a necessary mod-two letter-parity test.  It then checks all
cyclic cuts exactly for witnesses

```text
A U C U^(-1),        B U D U^(-1),
```

where `{A,B}={a,b}`, `{C,D}={c,d}`, both source gates lie in the same
coefficient copy, both target gates lie in the same coefficient copy, and the
formal carrier word `U` is literally identical.  Such a pair would imply
`[c,d]=U^(-1)[a,b]U=1`.

The thirteen MSI shards of job `16662507` completed normally.  Their exact
tested counts sum to

```text
1,036,800 + 887,040 + 887,040 + 1,013,760 + 1,036,800
+ 1,144,320 + 1,251,840 + 779,520 + 929,280 + 1,359,360
+ 1,144,320 + 887,040 + 1,121,280 = 13,478,400.
```

Every shard reports `hits 0`.  The single-carrier family is included as
carrier code zero.  The fence is limited to this local-feature coloring
family; it does not exclude arbitrary independent compound words in the nine
carrier slots.
