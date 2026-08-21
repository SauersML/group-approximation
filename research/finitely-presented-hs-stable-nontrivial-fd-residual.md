---
rg: 2
id: finitely-presented-hs-stable-nontrivial-fd-residual
kind: claim
title: Exhibit a finitely presented uniformly HS-stable group with nontrivial finite-dimensional residual
distinct_from:
  leavitt-steinberg-hs-stable: that asks only for stability of the binary Leavitt Steinberg group, whose finite-dimensional invisibility data must still be matched to a nontrivial abstract word.
  literal-mark-quotient-not-stable-in-finite-actions: that proves instability for permutation/Hamming models of a specific sofic quotient rather than normalized-HS stability.
---

OPEN.  Produce a finitely presented group `Gamma` and a word `w` satisfying

```text
w!=1 in Gamma,
pi(w)=I for every finite-dimensional unitary representation pi,
Gamma is uniformly flexibly stable in normalized Hilbert--Schmidt norm.
```

By `hs-stability-plus-fd-residual-forces-nonhyperlinearity`, this is a direct
nonhyperlinear witness.  It is enough that `w` be nontrivial in the ordinary
finite residual.  The analytic condition is the hard part: fixed-rank or
Fredholm-index defects dilute like `sqrt(r/d)`, and property `(T)` or
Frobenius stability alone does not supply dimension-free normalized-HS
stability.

## Attempts

- The minimally almost periodic criterion is the special case recorded by
  `map-matricial-stability-non-mf`; it demands much more finite-dimensional
  invisibility than is needed here.
- The binary Leavitt Steinberg candidate has strong finite-dimensional
  collapse data, but `leavitt-steinberg-hs-stable` remains open.
- A nontrivial finite residual is algebraically convenient, but the known
  non-residually-finite telescope examples are not thereby HS-stable.
