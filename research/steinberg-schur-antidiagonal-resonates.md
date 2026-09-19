---
rg: 2
id: steinberg-schur-antidiagonal-resonates
kind: claim
title: The corrected Schur antidiagonal has genuine cyclotomic resonances
invalidates:
  - steinberg-schur-divide-antidiagonal-recursion
distinct_from:
  steinberg-rank-one-schur-pivot-is-invertible: this blocks one recursive proof strategy but does not give a singular corrected matrix.
  steinberg-schur-four-transform-reduction-fails-p-seven-check: that finds an indexing error in the old reduction; this is a genuine zero coefficient in the corrected SRP7 endpoint system.
---

**ESTABLISHED RESONANCE FIREWALL.**  In the corrected endpoint system
`(SCE9)`, the first nontrivial row `j=3` is

```text
2q_2-(2^5-1)q_(p-3)=0.                                  (SAR1)
```

At `p=31`, the antidiagonal coefficient vanishes, and `(SAR1)` reduces to
`2q_2=0` without coupling `q_(p-3)`.  Thus the corrected antidiagonal is not
uniformly nonzero.  Any recursive Schur argument which divides by every
`2^(2j-1)-1` is invalid.  The resonance does not itself produce a nonzero
kernel vector, so the full determinant claim remains open.
