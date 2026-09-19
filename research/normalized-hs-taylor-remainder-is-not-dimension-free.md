---
rg: 2
id: normalized-hs-taylor-remainder-is-not-dimension-free
kind: claim
title: Second derivatives of unitary word maps have no dimension-free bound in normalized Hilbert--Schmidt norm
invalidates:
  - iwahori-newton-closes-near-sector-proof
distinct_from:
  iwahori-uniform-infinitesimal-rigidity: that is the first-order (linear) gap for the Iwahori mismatch map, which is a statement about a fixed linear operator and survives; this concerns the second-order Taylor remainder that the Newton integration step needs and shows it is not dimension-free in the normalized HS metric.
  iwahori-torsion-multiplicity-stratum-reconciliation: that records the O(d^(-1/2)) separation between different torsion-multiplicity strata; this shows the same rank-one phenomenon already defeats the Taylor step INSIDE one stratum.
---

Let `F` be any map built from words in unitaries `U_1, ..., U_k in U(d)` and
fixed matrices (for instance the Iwahori compatibility map), and perturb
along `U_j(t) = U_j exp(t X_j)` with `X_j` anti-Hermitian.  Each term of the
second derivative `F''[X, X]` has the form `A X_i B X_j C` with `A, B, C`
products of unitaries, so

```text
|| F''[X, X] ||_2 <= L || X ||_op || X ||_2                        (NHT1)
```

with `L` depending only on the word lengths.  **There is no bound of the
form `|| F''[X, X] ||_2 <= L' || X ||_2^2` with `L'` independent of `d`**,
already for the one-letter word `F(U) = U^2` at `U = 1`, where
`F''[X, X] = 4 X^2`: for `X` anti-Hermitian of rank one with eigenvalue
`i pi`, in normalized Hilbert--Schmidt norm

```text
|| X ||_2 = pi / sqrt d,    || X^2 ||_2 = pi^2 / sqrt d,
|| X^2 ||_2 / || X ||_2^2 = sqrt d -> infinity.                     (NHT2)
```

**Consequence.**  The route `iwahori-newton-closes-near-sector-proof`
asserts "Fixed word length bounds the second derivative in normalized
Hilbert--Schmidt norm" and then uses Taylor's formula
`def >= sigma_0 D - (L/2) D^2` with `D` the normalized-HS distance to the
compatible locus.  By `(NHT2)` that inequality has no dimension-free
constant, so the conclusion `D <= 2 def / sigma_0` for `D <= sigma_0 / L` is
unsupported and the route is invalid; `iwahori-newton-closes-near-sector`
returns to OPEN.  The rank-one perturbation is a rotation of one flag line
and stays inside a fixed torsion-multiplicity stratum, so the stratum
restriction of that node does not avoid it.  The nearest true statement is
the same Taylor argument under an OPERATOR-norm proximity hypothesis
`|| X ||_op <= sigma_0 / (2L)`, which gives `def >= (sigma_0 / 2) D` with
`def` and `D` still measured in normalized HS -- a genuine but strictly
weaker theorem than the near sector of `iwahori-local-global-defect-question`
requires, since that question is posed in the HS metric.
