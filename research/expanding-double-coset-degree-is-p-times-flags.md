---
rg: 2
id: expanding-double-coset-degree-is-p-times-flags
kind: claim
title: The expanding double coset has degree p times the flag count, so the wired pair averages over forty-two words
distinct_from:
  hecke-averaging-realizes-commutant-expectation: that proves the contraction with the coset count L as a symbolic constant; this evaluates L in closed form, making the lazy average and the enemy fingerprint fully numeric for the wired pair.
  single-hecke-average-isometry-for-lambda-central-unitaries: that is the open one-inequality form of the collapse; this pins its combinatorial data — forty-three over one-hundred-sixty-eight is the exact enemy value to beat at (n, p) = (3, 2).
---

Let `n = 3`, `Lambda = SL_3(Z)`, `gamma_0 = h = diag(p, 1, p^(-1))`.
Then the number of left cosets in the expanding double coset is

```text
L = [Lambda : Lambda cap h Lambda h^(-1)]
  = p (p + 1) (p^2 + p + 1).                                     (DC1)
```

For the wired pair `p = 2`: `L = 2 * 3 * 7 = 42`, so the lazy Hecke
average `S` of `hecke-averaging-realizes-commutant-expectation` is a
convex combination of the identity (weight `1/2`) and `42` explicit
integer-matrix conjugations (weight `1/84` each), and the exact
quasi-regular enemy fingerprint of
`single-hecke-average-isometry-for-lambda-central-unitaries` is

```text
|| S(k) ||_2^2 = 1/4 + 1/(4L) = 43/168 = 0.2559...              (DC2)
```

while the collapse asserts the value `1` for every `Lambda`-central
unitary of a regular-trace matrix model.  The gap between `43/168`
and `1` is the entire content of the higher-rank goal edge, now a
statement about one average of forty-three explicitly listable
terms.
