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

For the literal simple-Weyl denominator rectangle, the ambient section words
do compare the paths.  `sl3-raw-weyl-rectangle-pins-only-equal-rank-corners`
proves that their relative loop is exactly trivial and gives the sharp
source-Gram identity transferring this to any equal-rank decoded corner.
The transfer fails for the current shell atom for a concrete reason: its
trace is `1/42`, while the available raw lamp and positive two-lamp atoms
have traces `1/2` and `1/4`.  The remaining gate is therefore a rank-matched
joint-atom decoder or a non-pointwise authentication map, not another loop
identity.

An exact finite packet cannot supply that rank-matched decoder.
`sl3-one-over-forty-two-packet-is-external-or-folded` rules out an internal
finite-character idempotent of trace `1/42` and shows that a 21-atom quotient
refinement has only two outcomes: a `C`-fixed atom is `A`-fixed by co-density,
whereas a moving atom no longer carries the raw section identities.  The
rank-matched source must therefore be a genuinely approximate
matrix-coordinate object or a non-finite packet, not an exact finite
selector attached to the lamp.

Nor can one replace the finite selector by a fixed spectral polynomial.
`fixed-spherical-polynomials-have-no-42nd-projection` uses the
connected tempered Satake spectrum to show that a fixed Hecke polynomial
which becomes an idempotent in canonical regular moments has trace zero or
one.  The only spherical trace-`1/42` projections are discontinuous Borel
cuts requiring unbounded depth; finite moment tables again admit atomic
quadrature.  The surviving rank source therefore needs an unbounded
conductor filtration with presentation-uniform section control.

One denominator action cannot provide that control by itself.
`single-denominator-borel-cuts-have-a-rohlin-escape` constructs
trace-`1/42` Rohlin cuts with vanishing covariance defect for every diffuse
abelian algebra preserved by one aperiodic denominator automorphism, and a
diagonal staircase absorbs arbitrary finite polynomial propagation costs.
Thus the remaining arithmetic input must prove that the spherical/conductor
cut is not an ordinary same-carrier invariant algebra, or invoke several
Weyl-conjugate denominator actions with a genuine joint gap.

The literal factor swap gives a useful minimal reformulation but no hidden
character proof.  `arithmetic-double-swap-extension-is-binary-coset-wreath`
identifies

```text
(A *_C A) rtimes C_2
  = A *_C (C x C_2)
  = ( *_(A/C) C_2 ) rtimes A.
```

Canonical microstates pass both ways by an explicit two-block
symmetrization, the fold mark becomes the real-trace commutator `[h,s]`, and
every exact finite-dimensional representation centralizes `s` against all
of `A`.  Thus this removes the target phase and exposes one balanced
involution, but excluding its canonical microstates is exactly the original
problem rather than a consequence of finite-extension character theory.

Nor do finite joint moments of this involution and its conjugates help.
`finite-swap-conjugate-moments-do-not-fold-arithmetic-double` proves that
every finite such word/projection moment table has an exact finite regular
model, using residual finiteness of a finite free product of binary lamps.
The genuinely missing datum is therefore the joint approximate extension by
the arithmetic actor, not another canonical block-swap character
decomposition.
