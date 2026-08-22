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

The canonical block-swap character decomposition also stops short.
`finite-spherical-moments-do-not-fold-regular-double` identifies its
restriction to the commutative `2`-adic spherical Hecke algebra with the
quasi-regular Plancherel state.  Every finite family of those moments has
finite atomic diagonal quadratures, including the nonfolded one-average
value `43/168`.  Property (T) isolates the trivial spherical point but does
not force an abstract quadrature onto it.  The surviving content is exactly
that the quadrature must extend to one approximately multiplicative regular
matrix assignment of the full double; exact extension is where finite
co-density folds.

Nor does adjoining every bounded-depth dyadic Clifford type create the
missing extension by itself.  The exact tensor escape in
`spherical-quadrature-tensors-through-clifford-folner-windows` combines each
finite spherical quadrature with a conjugate-doubled coweight Folner box.
Every fixed local Clifford cycle and every cross-commutation relation then
has vanishing defect, while the Hecke average converges to `43/168`.  The
remaining gate is therefore a non-tensorial same-carrier arithmetic word (or
an additive multi-path interference cell), not another finite list of
separate spherical and Clifford tests.

The same fence survives the first apparently mixed construction.
`central-hecke-controlled-multipaths-remain-sectorwise` proves that an
additive elementary/Hecke operator `sum_a p_a V_a`, controlled by the atoms
of one spherical chart, is only an orthogonal direct sum: every word and
every normalized-Hilbert--Schmidt defect decomposes sectorwise.  The minimal
unfenced relation must therefore authenticate a noncommuting second chart or
put two elementary-matrix paths into one common block so that their cross
term is visible.

Even one such block does not suffice abstractly.
`two-sl3-shell-charts-have-a-rotated-flip-escape` rotates the two coordinate
shell PVMs into a genuinely noncommuting pair and constructs an exact full
off-diagonal transporter between them, while their authentication deficit is
still `(41/42)cos(t)^2`.  Thus the smallest surviving same-corner datum is a
three-chart arithmetic triangle with two competing returns (a Bargmann or
loop-holonomy term), unless the raw denominator section identities can pin
the two-chart transporter directly.

Nor is an unpaired triangle enough.
`three-chart-loop-retains-free-multiplicity-holonomy` computes the exact
gauge-invariant cross term between two corner returns, but an unrestricted
multiplicity unitary realizes every value in the closed unit disk while all
chart fullness and covariance equations remain exact.  The presentation must
make two native arithmetic return paths occur coherently in one block and
control their relative trace; simply authenticating the paths separately
leaves the loop gauge free.
