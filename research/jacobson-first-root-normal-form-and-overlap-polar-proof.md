---
rg: 2
id: jacobson-first-root-normal-form-and-overlap-polar-proof
kind: route
title: Correct nine approximate root coordinates relative to F and polar-align the boundary packet on the full intersection
target: jacobson-first-root-packet-admits-coherent-relative-correction
requires:
  - jacobson-mixed-cells-reconstruct-full-first-level-root-packet
  - jacobson-boundary-cell-reconstructs-finite-root-packet
artifacts:
  - research/artifacts/jacobson-first-root-packet-coherent-rounding-2026-09-08.md
---

The TS and braid errors control all generators of the two order-24
stabilizers. Their Cayley diameter is at most 23, giving orbit
covariance error `epsilon`. Transport the two boundary addition laws
and compare the two expansions of a bilinear sum to bound every root
commutator. An ordered nine-root normal form then has multiplication
error `648epsilon` and covariance error `5409epsilon`. Together these
give a unital approximate representation of `P` with uniform defect
`delta=6057epsilon`.

This map is exactly the original `F` representation and exactly the
old boundary representation on `I`: the four `N_0` coordinate roots
use transporters in the shared finite subgroups, and the other two
boundary root coordinates already lie in `A_Q` inside `F`.

Apply the finite-group relative correction lemma to `P` while fixing
`F`. The corrected representation and old `J` restriction on `I`
are exact and within `85delta`. The polar factor of their averaged
intertwiner is within `170delta` of the identity and centralizes
`P_Q x K_P`. Conjugate the entire `J` representation by it.
This aligns `I`, preserves the original packet, and moves the one
matrix `H` by at most `340delta`. Fixed-word telescoping gives the
remaining error bounds. The now-exact cross commutations identify the
TS norm with its pure tail norm.
