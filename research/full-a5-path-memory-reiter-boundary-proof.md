---
rg: 2
id: full-a5-path-memory-reiter-boundary-proof
kind: route
title: Transport atomwise bases along paths and compute the unmatched multiplicity mass
target: full-a5-path-memory-kills-holonomy-but-not-reiter-boundary
requires:
  - two-site-a5-plancherel-center-separates-mark
  - no-invariant-mean-on-coset-space
  - finite-cylinder-mixed-traces-kill-normalizer-holonomy
---

For the exact interior assertion, if `e_(omega,j)` is an atomwise basis at
the root, use `U_a e_(omega,j)` on the `a`-copy.  Exact multiplication gives

```text
U_s U_a e_(omega,j)=U_(sa)e_(omega,j),
```

which is `(APM2)` and proves simultaneous path composition.  For an
approximate representation, telescoping the fixed representative words
bounds the same difference by the sum of their normalized-HS relation
defects; taking a direct sum preserves the weighted quadratic average.

For each `a`, at most `min(m_a,m_(sa))` copies can be paired with the target
label `sa`.  Summing and dividing by `M` gives the left side of `(APM3)`.
The elementary identity

```text
sum_a min(mu(a),mu(sa))
 =sum_a (mu(a)+mu(sa)-|mu(a)-mu(sa)|)/2
```

gives its right side.  Tensoring every summand with a fixed finite center
packet multiplies both matched and total dimensions by the same number, so
the ratio is unchanged.

If `(APM5)` failed along a sequence, `(APM4)` would hold after diagonalizing
over the finite generating set.  The finitely supported measures would be a
Reiter sequence and hence define an invariant mean on `G`.  The pinned
property-`(T)` actor is infinite, so its regular action admits no invariant
mean; equivalently it is nonamenable.  This contradiction proves `(APM5)`.

