---
rg: 2
id: nonaffine-relation-alone-cannot-force-affine-safe-factor-support
kind: claim
title: No nonaffine relation can force affine-safe support by factoriality alone
distinct_from:
  extreme-traces-and-local-pruning-do-not-select-fano-caps: that gives the concrete seven-point R-star example; this proves the universal statement for every finite nonaffine relation.
  fano-cap-range-sections-cannot-encode-nonaffine-relations: that obstructs cap-range pp witness sections; this concerns the local tracial algebra before any reduction gadget is chosen.
---

ESTABLISHED.
Let `R subseteq F_2^k` be a finite relation with `n=|R|>=2`.  The universal
algebra of two disjoint `R` contexts is

```text
C^R * C^R.                                                       (NRS1)
```

It has an extreme finite-dimensional trace in which both local supports are
all of `R`.  Map the first context atoms to the diagonal rank-one projections
of `M_n(C)` and the second to their Fourier conjugates.  The two MASAs
generate `M_n(C)`, since diagonal atoms `e_i` and the Fourier uniform atom
`q` satisfy

```text
e_i q e_j=(1/n)e_(ij).                                           (NRS2)
```

The resulting GNS algebra is the factor `M_n(C)`, so the trace is extreme,
and every local atom has trace `1/n`.

If `R` is nonaffine, then `Aff(R)` is not contained in `R`; hence this extreme
support is not affine-safe.  Therefore no choice of a nonaffine NP-hard
Boolean relation can make all factorial or irreducible perfect supports
affine-safe by a relation-local invariant alone.  Any successful
fixed-language compiler must use special global overlap geometry of its HALT
instances.
