---
rg: 2
id: titz-witzel-cyclic-affine-ansatz-has-linear-defect
kind: claim
title: The natural cyclic-affine exact-square ansatz for the Titz--Witzel gate has asymptotically maximal coupling defect
distinct_from:
  titz-witzel-sofic-gate-has-only-seven-relators: That removes five redundant relators and leaves five genuinely approximate coupling equations; this tests and exactly excludes the most symmetric cyclic-affine attempt to solve those equations.
  titz-witzel-sparse-defect-needs-dense-generator-surgery: That proves a general lower bound on generator edits from exact finite actions; this computes all twelve defects in a specific maximally separated affine family.
artifacts:
  - research/artifacts/titz-witzel-cyclic-affine-csp-search-2026-08-26.md
---

**THEOREM (EXACT ANSATZ COMPUTATION).**  Let `n>=5` be odd, work on
`Omega_n=Z/nZ`, and put `h=(n+1)/2`, so that `2h=1` in `Z/nZ`.  For any
`a in Z/nZ`, define

```text
y(i)=i+1,                   x(i)=-i+a,                   z(i)=i+h.       (TCA1)
```

For the words `A,B,C,D,E,F,S,H` in `(TWS3)`, all seven square relators

```text
A^2, B^2, C^2, E^2, F^2, S^2, H^2
```

hold exactly.  The normalized Hamming defects of the remaining five
relators, in their `(TWS4)` order, are exactly

```text
1-1/n,            1-1/n,            1,            1-1/n,            1. (TCA2)
```

At the same time `d_H(y^8,1)=1`.  Thus this family realizes the marked
separation objective as strongly as possible and lies on the exact
square-relator locus, but it does not even asymptotically approach any of
the five essential coupling equations.

This is a no-go only for the translation-square-root affine ansatz `(TCA1)`.
It is not a lower bound for arbitrary permutation triples and does not decide
the open soficity gate.

---

### Proof

titz-witzel-cyclic-affine-ansatz-proof
