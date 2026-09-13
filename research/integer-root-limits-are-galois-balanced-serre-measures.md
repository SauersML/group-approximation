---
rg: 2
id: integer-root-limits-are-galois-balanced-serre-measures
kind: claim
title: A compactly supported measure is a limit of integer-matrix real spectra exactly when it obeys the Serre inequalities and its algebraic atoms are balanced totally real algebraic integers
distinct_from:
  integral-spectral-limits-satisfy-serre-inequalities: that proves only the Serre inequalities for limits of symmetric integer spectra; this adds Galois balance of atoms and proves the converse, for integer matrices with real spectrum
  serre-class-measures-are-integral-spectral-limits: that asserted the converse for the whole Serre class and symmetric matrices, and is refuted; this is the corrected converse, with balance added and symmetry dropped
  smith-serre-measures-are-conjugate-limits: that is the literature theorem for sequences of distinct orbits, whose limits are atomless; this characterizes all limits of integer spectra, atoms included, and is derived from it
artifacts:
  - research/artifacts/determinant-integer-root-limits-2026-09-12.md
---

**ESTABLISHED** by `integer-root-limits-galois-balanced-proof`. Unreviewed.

Let `mu` be a compactly supported probability measure on `R`. The following are
equivalent.

1. **Integer root limit.** There are `C` and integer matrices with real spectrum
   in `[-C, C]` whose normalized eigenvalue distributions converge weakly to
   `mu`. Equivalently, monic integer polynomials with real roots in `[-C, C]`
   whose root distributions converge to `mu`.
2. **Balanced Serre class.** `integral_(Q != 0) log|Q| d mu >= 0` for every
   nonzero `Q in Z[x]`, and every atom of `mu` at an algebraic number is a
   totally real algebraic integer whose conjugates all carry the same mass.

**Intrinsic form of the continuous part.** Write
`mu = sum_O w_O nu_O + mu'`, balanced atoms on totally real orbits plus a
remainder `mu'`. Then (1) holds iff

```text
integral log|Q| d mu' >= 0    for every nonzero Q in Z[x],
```

with the integral over all of `R`. Such a `mu'` is atomless
(`serre-class-atoms-obey-degree-bound`).
- This answers, for limits of integer matrices with real spectrum, the question
  Thom poses after Theorem 5.4 of arXiv:math/0701294v3: "characterize the
  continuous parts of the spectral distribution function intrinsically".
- Thom's integer operators (normal integer approximants) satisfy (2). Whether
  every measure satisfying (2) has normal integer approximants is not settled.

**For groups** (artifact Section 4): every self-adjoint integral group-ring
spectrum over `G` is an integer root limit iff `G` satisfies Lück's determinant
conjecture and `integral-group-ring-eigenvalues-are-galois-balanced` holds for
`G`.
