---
rg: 2
id: nonhyperlinear-from-marked-extensive-index-energy
kind: route
title: Marked positive-density index energy excludes hyperlinear microstates
target: non-hyperlinear-group
requires: [extensive-cosystolic-index-defect, index-density-is-amplification-stable]
---

Take the presentation, nontrivial marked word `z`, constants and syndrome
assignment supplied by `extensive-cosystolic-index-defect`.

If the presented group were hyperlinear, apply the definition to a finite
window containing the generators, all relators and `z`.  There would be
unitary tuples `U_n` with

```text
sum_(r in R) ||r(U_n)-1||_2^2 -> 0
```

while `z`, being nontrivial, stays separated from the identity by a fixed
positive amount after passing to a tail (in the regular-character
normalization its distance tends to `sqrt(2)`).  Thus the marked hypothesis of
the claim applies for all large `n`.

The claim then gives at least `c d_n` nonzero syndrome carriers and the energy
payment

```text
c <= #(carriers)/d_n
  <= C * sum_(r in R) ||r(U_n)-1||_2^2,
```

contradicting convergence of the relator defect to zero.  Hence the presented
group is not hyperlinear.

`index-density-is-amplification-stable` records why the left-hand quantity is
not diluted by the standard tensor-amplification freedom of normalized HS
models.  The actual contradiction, however, comes from the energy-payment
inequality; density without that inequality would obstruct only repair, not
existence.
