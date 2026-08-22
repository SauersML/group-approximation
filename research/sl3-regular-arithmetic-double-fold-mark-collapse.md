---
rg: 2
id: sl3-regular-arithmetic-double-fold-mark-collapse
kind: claim
title: Regular microstates of the SL3 arithmetic double collapse one fold-kernel mark
distinct_from:
  projective-trace-square-transfer-for-sl3-pair: that quantifies over every approximate representation of A and every auxiliary unitary; this asks only about canonical-trace microstates of the fixed double A amalgamated over C with A.
  sl3-hnn-admits-no-amalgamated-free-haar-unitary: that forbids a Haar unitary with its full amalgamated-free B-valued distribution; this uses only the restriction to the adjacent-vertex double and one fold-kernel word.
  no-exact-quasi-regular-leak: that forbids a subgroup-central unitary with an exact coefficient profile against every element of A; this asks only for collapse of one fixed word inside full regular-character microstates of the double.
---

OPEN.  Put

```text
C=SL_3(Z),   A=SL_3(Z[1/2]),   D=A *_C A,
w=i_0(h)i_1(h)^(-1),   h=diag(2,1,1/2).
```

For every sequence of unitary assignments `sigma_n` with vanishing defect
for a fixed finite presentation of `D` and canonical character on `D`,

```text
|tr(sigma_n(w))| -> 1.                                        (RDF1)
```

This is the genuinely minimal regular-trace transfer statement exposed by
the HNN lane.  The quantifiers no longer include arbitrary assignments,
arbitrary auxiliary unitaries, or assignments merely regular on the vertex
group.  They include exactly the full regular microstates of the smaller
double.  Since `w!=1` by amalgam normal form, canonical regularity also
requires `tr(sigma_n(w))->0`, contradicting `(RDF1)`; so the claim forbids
those microstates.

## Exact boundary and remaining gap

`sl3-arithmetic-double-finite-representations-fold` proves the zero-defect
version with the much stronger conclusion that the whole fold kernel is
killed.  The proof is the block-swap/co-density argument.  The unresolved
step is only its full-regular normalized-HS promotion:

```text
almost representation of D + canonical character
    => their relative h-word has trace modulus near one.       (RDF2)
```

The joint near-exact sector is also complete.
`sl3-arithmetic-double-near-exact-vertices-fold-projectively` proves
`(RDF1)` whenever BOTH full vertex assignments approach exact
finite-dimensional representations, with a dimension-free estimate.  Hence
every enemy initially had to keep at least one whole `A` vertex uniformly
outside the exact representation variety.

The subsequent anchor theorem
`sl3-double-one-near-vertex-forces-joint-near-exactness` closes the mixed
sector too: if either vertex is near exact, the amalgamating relations,
relative property (T), and the Bezout exponent-sum argument correct the other
vertex to the same representation.  Therefore every surviving enemy has
BOTH full `A` vertices uniformly far from every exact finite-dimensional
representation along a subsequence.  The minimal remaining correction
terminal is `sl3-canonical-double-has-a-correctable-vertex`.

Canonical character does not make the known unnormalized Frobenius tools
applicable.  `sl3-canonical-double-replication-escapes-every-frobenius-basin`
preserves the full canonical character and every normalized defect while
scaling unnormalized Frobenius defects above any prescribed threshold.  Thus
2-Kazhdan/Frobenius stability can enter only through a global
replica-homogeneous correction inequality, not by a trace-conditioned change
of normalization.

This is strictly narrower than `projective-trace-square-transfer-for-sl3-pair`.
That universal claim would apply to the block diagonal of the two vertex
assignments and the swap unitary, and immediately give `(RDF1)`; the converse
has no reason to hold because `(RDF1)` sees only double-regular assignments.

The symmetric-double MF theorem does not decide `(RDF1)`.  It provides an
operator-norm corona embedding under an MF hypothesis, but does not preserve
the canonical trace on the nonamenable amalgam.  Thus this terminal respects
the trace firewall in `sl3-hnn-sits-in-shulman-symmetric-double` rather than
reintroducing the invalid MF-to-hyperlinear implication.
