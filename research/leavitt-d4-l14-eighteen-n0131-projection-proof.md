---
rg: 2
id: leavitt-d4-l14-eighteen-n0131-projection-proof
kind: route
title: Collapse the normal 131 projection presentation by two composite roots
target: leavitt-d4-l14-eighteen-n0131-projection-core
requires:
  - leavitt-d4-l14-eighteen-winner-profile-has-two-classes
---

Coordinate Tietze elimination of all ten nonempty raw copy projections leaves
seven generators and three relators.  Introduce

```text
p = (-8,-6,-2,3,5),       B = (-7,-5,-3).
```

Eliminating the once-occurring generators `8` and `7` gives, by literal free
reduction,

```text
p^3,
B p^2 B p^3 B^-1,
p^-6 B p^-2 B p^2.
```

Thus `p^3=1`; the second relator becomes `Bp^2`, so `B=p`; and the third
becomes `p^-4`, hence `p^2=1`.  Coprimality of 2 and 3 gives `p=B=1`.
The five remaining free coordinates may be taken as `g1,g2,g4,g5,g11`.

The compression script independently reconstructs the raw projections,
asserts the coordinate-Tietze residuals, asserts the two composite-root
substitutions and their three displayed relators, and checks that its final
five-generator images kill every raw projection.  Substitution into the full
nonabelian words gives lengths

```text
R0=0, R2=13, R4=39, K=33.
```

Every copy projection of `R2,R4` is empty.  MSI job `16686624` now runs the
all-maximal carrier intersection.  No boundary or survival claim is made here.
