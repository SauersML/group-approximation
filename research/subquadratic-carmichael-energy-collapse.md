---
rg: 2
id: subquadratic-carmichael-energy-collapse
kind: claim
title: Subquadratic total Carmichael energy collapses a conjugacy packet onto its cube defect
artifacts:
  - research/artifacts/thompson-subquadratic-carmichael-energy-2026-08-24.md
distinct_from:
  thompson-carmichael-collapse: that assumes a uniform bound at one scale `epsilon` on every cube and every pair defect and concludes `||B-I||_2<=2epsilon`; this assumes nothing about any individual pair, only that the total squared edge energy is `o(M^2)`, and concludes the scale-free relative inequality `||B-I||_2<=||B^3-I||_2`.
  bounded-area-high-chromatic-conjugacy-collapse: that produces its close conjugate pair from an unbounded chromatic number and then spends a uniform per-edge relator-area certificate on the one monochromatic edge; this produces the close pair by counting energy against the number of same-cell pairs, so no per-edge certificate exists or is used.
  a5-carmichael-triangle-covers-involution-kernels: that is a fixed spectral-gap inequality inside one copy of `A_5` bounding three separate edge channels from below; this is an asymptotic packing and counting theorem about arbitrarily large packets inside one fixed matrix dimension.
  carmichael-energy-uniform-criteria-incomparable: that compares this criterion with the uniform one and shows neither implies the other; this is the criterion itself.
---

All Hilbert--Schmidt norms are normalized, `||A||_2^2=(1/d)tr(A^*A)`.

## The two-matrix kernel

For any `B in U(d)` and any `A,C in U(d)` that are unitary conjugates of `B`,

```text
||B-I||_2 <= ||B^3-I||_2 + 2||A-C||_2 + ||(AC)^2-I||_2.       (CP)
```

This is the reusable engine.  It charges no relator, no word, and no filling
area: the conjugating unitaries are arbitrary and their word length never
appears.

## The collapse theorem

Let `B in U(d)`.  Suppose there is an unbounded set of integers `M` and, for
each such `M`, unitaries `X_1,...,X_M in U(d)` all conjugate to `B`, with

```text
E_M := sum_(1<=i<j<=M) ||(X_iX_j)^2-I||_2^2 = o(M^2).        (ACE)
```

Then

```text
||B-I||_2 <= ||B^3-I||_2.                                     (SCE)
```

In particular `B^3=I` forces `B=I`.

## Effective form

Let `N(d,B,r)` be the number of balls in a finite cover of the compact
conjugacy orbit `O(B)={WBW^*: W in U(d)}` by normalized-HS balls of radius
`r`, and put

```text
S_M = M^2/(2N(d,B,r)) - M/2.
```

Then for every `r>0` and every `M>N(d,B,r)`,

```text
||B-I||_2 <= ||B^3-I||_2 + sqrt(E_M/S_M) + 4r.                (EFF)
```

`(SCE)` is `(EFF)` after `M -> infinity` at fixed `r`, then `r -> 0`.

`N(d,B,r)` grows with `d`, but the matrix dimension is fixed **before** `M`
tends to infinity, so the covering number never competes with the packet size.
There is no dimension-versus-defect packing rate to control, which is what
distinguishes this from every exactification route in the region.

## Scope

Two limits are structural, not repairable.

The conclusion is **vacuous for involutions**: `B^2=I` gives `B^3=B`, so
`(SCE)` reads `||B-I||_2<=||B-I||_2`.  The order-three mark is therefore
load-bearing, and this is exactly why
`affine-clone-model-defeats-pure-thompson-prefix-error-spreading`, whose mark
`e_empty` is an involution, does not bear on the theorem.

The inequality is **sharp**: `B^4=I` gives `B^3=B^*` and hence equality.  A
packet witnessing `(ACE)` at such a `B` exists (see
`carmichael-energy-uniform-criteria-incomparable`), so `(SCE)` cannot be
strengthened to `B=I` without separate control of `||B^3-I||_2`.

## Use

For a finite presentation `<X|R>` in which `b^3` is a relator of bounded area,
`||U(b)^3-I||_2 <= C_b def_R(U)`, so `(SCE)` upgrades to

```text
||U(b)-I||_2 <= C_b def_R(U)
```

for every model satisfying `(ACE)`.  Applied to the Bleak--Quick mark
`b=(01 10 11)` of Thompson `V` this is the collapse used by
`thompson-v-one-word-ceiling-from-subquadratic-energy`; the open input is
`r5-subquadratic-carmichael-energy`.
