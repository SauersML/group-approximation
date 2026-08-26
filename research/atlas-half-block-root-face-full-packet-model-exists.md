---
rg: 2
id: atlas-half-block-root-face-full-packet-model-exists
kind: claim
title: Growing full-coefficient Atlas models exist on the first-root half-block commutant face
distinct_from:
  atlas-order-one-weyl-common-root-exists: that restricts the two coefficient variables to one Heisenberg/Weyl relation and is refuted by the first relator; this permits arbitrary noncommutative two-unitary moments but imposes the exact positive face actually cut out by that relator.
  atlas-first-root-relator-is-half-block-commutant-face: that identifies the necessary half-block equation from one relator; this asks to solve every remaining packet equation while staying on that face and retaining full coefficient algebras.
---

**OPEN.**  Do there exist dimensions `r_n -> infinity` and pairs
`Z_(1,n),Z_(2,n) in U(r_n)` such that

```text
C*(Z_(1,n),Z_(2,n)) = M_(r_n)(C),                    (HRM1)
Omega(Z_(1,n),Z_(2,n)) -> 0,                         (HRM2)
max_(s in T_St \ {root_12_1e})
  ||pi_(U_(Z_1,Z_2))(s)-I||_2 -> 0?                  (HRM3)
```

By `atlas-first-root-relator-is-half-block-commutant-face`, `(HRM2)` is
exactly the first packet equation.  Thus this is the unrestricted
non-Heisenberg survivor of the refuted common-Weyl-root ansatz, expressed on
the smallest positive face currently forced by a literal rank-five word.

The condition does not assume that `Z_1,Z_2` commute.  Indeed `(HRM1)` rules
out a commutative coefficient algebra.  By
`atlas-root-triangle-is-heisenberg-character-fibers`, `(HRM3)` further
localizes the search to the `D8` multiplicity summands and central-character
atoms `(HTF6)`--`(HTF8)`: the neighboring root variables preserve those
atoms and satisfy the scalar Pauli signs `(HTF7)`.  The remaining search is
whether the other roots can couple these noncommutative character fibers
while satisfying the other packet entries.

ROUTES
atlas-half-block-root-face-model-proves-leavitt-hyperlinear
