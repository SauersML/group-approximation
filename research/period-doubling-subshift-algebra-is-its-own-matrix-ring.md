---
rg: 2
id: period-doubling-subshift-algebra-is-its-own-matrix-ring
kind: claim
title: The period-doubling subshift algebra is isomorphic to its own two-by-two matrix ring, so its elementary group is EL_(3·2^j) over the same ring
artifacts:
  - research/artifacts/period-doubling-elementary-group-phase-extraction-2026-09-12.md
distinct_from:
  minimal-subshift-algebra-is-simple-lef-ring: that proves simplicity and the LEF property for every infinite minimal subshift algebra; this proves a ring isomorphism A ≅ M_2(A) for the period-doubling subshift, using its odometer phases and decimation.
  kazhdan-groups-without-fd-reps-violate-two-root-identity: that uses the unital copies of M_(2^j)(F_2) inside the same algebra to kill finite-dimensional representations; this identifies the corner over the even phase with the whole algebra, so the algebra is its own matrix ring.
  anti-central-ternary-summand-contains-its-matrix-ring: that places a unital two-by-two matrix ring inside an anti-central summand of a ternary Leavitt group algebra; this is an isomorphism for a stably finite crossed product of a Toeplitz subshift.
---

Let `z(n) = nu_2(n) mod 2` for `n != 0`, `z(0) = 0`, let `X` be its orbit closure under the shift
`T`, and put

```text
A = LC(X, F_2) ⋊_T Z.
```

Then `A ≅ M_2(A)` as unital rings. Consequently `A ≅ M_(2^j)(A)` for every `j`, and

```text
EL_3(A) ≅ EL_(3·2^j)(A)      for every j >= 0.
```

The matrix units are `chi_(P_(j,a)) u^(a-b)`, where `P_(j,a)` is the clopen set of points of odometer
phase `a mod 2^j`. The corner over the even phase is the crossed product of the induced system
`(P_(1,0), T^2)`, and decimation `x -> (1 + x(2i))_i` conjugates that system onto `(X, T)`.

`EL_3(A)/Z` is the simple Kazhdan LEF group of `simple-kazhdan-lef-group-from-minimal-subshift` for
this subshift. So that group has the same matrix self-similarity as the binary Leavitt unit group,
which is `GL_n` of its Leavitt algebra for every `n`. The artifact's Section 6 records, as commentary,
that the LEF models exclude inner corner compressions, which the Leavitt prefix codes do provide.
