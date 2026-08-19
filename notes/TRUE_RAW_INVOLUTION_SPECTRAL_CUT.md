# The raw word supplies an intrinsic positive-density coefficient cut

Date: 2026-08-13

## 1. Exact algebraic result

Let `r` be the scalarized raw swap in the characteristic-two Leavitt atlas.
Its displayed rank-four matrix is

\[
 r=
 \begin{pmatrix}
 p_0&0&0&s_1\\
 0&1&0&0\\
 0&0&1&0\\
 t_1&0&0&0
 \end{pmatrix}.
 \tag{RSC1}
\]

The lower-left sign in the general-ring raw matrix disappears in
characteristic two.  The Leavitt identities give

\[
 r^2=1,
 \qquad r\ne1.
 \tag{RSC2}
\]

Both statements are now kernel-checked in
`GroupApproximation/Leavitt/RawSwapCompressors.lean` as
`rawInvolutionWord_sq` and `rawInvolutionWord_ne_one`.  The same file already
proves

\[
 [r,\alpha(\mathrm{Core})]=1,
 \tag{RSC3}
\]

where `alpha` is the proper binary compression implemented by the comb
compressor `u`.

Thus the raw word is not merely a convenient transport detector.  It is a
nontrivial involution in the relative commutant of the compressed core.

## 2. Hyperlinear consequence

Assume hypothetically that the atlas group has a trace-preserving embedding
in a tracial matrix ultraproduct.  Write the image of `r` by the same letter.
Because `r` is a nonidentity group element, its canonical trace is zero.
Since it is a unitary involution, it is self-adjoint, and

\[
 e={1-r\over2}
 \tag{RSC4}
\]

is an orthogonal projection satisfying

\[
 \boxed{\tau(e)=\frac12.}
 \tag{RSC5}
\]

This projection is intrinsic over the complex tracial model.  It is not one
of the invalid characteristic-two XOR sums used to display `p_11` or
`p_001`.  Moreover `(RSC3)` gives

\[
 e\in \pi(\alpha(\mathrm{Core}))'.
 \tag{RSC6}
\]

Therefore the raw packet supplies a canonical, positive-density cut in the
coefficient relative commutant before any projection-recovery theorem is
invoked.

## 3. The exact commutant self-compression

Put

\[
 C=\pi(\mathrm{Core})',
 \qquad D=\pi(\alpha(\mathrm{Core}))'.
 \tag{RSC7}
\]

Because `alpha(Core)` is a subgroup of `Core`, and because `u` implements
`alpha`,

\[
 C\subseteq D,
 \qquad D=\pi(u)C\pi(u)^*.
 \tag{RSC8}
\]

Equation `(RSC6)` places `e` in `D`, while

\[
 e_0=\pi(u)^*e\pi(u)\in C,
 \qquad \tau(e_0)=\frac12.
 \tag{RSC9}
\]

At exact finite matrix coordinates, any inclusion of finite-dimensional
commutant algebras which are unitarily conjugate has equal vector-space
dimension and hence is equality.  If `(RSC8)` could be recovered
coordinatewise, then every element of `D`, including `r`, would already
commute with the full core.  The explicit raw conjugation identities show
that `r` moves named uncompressed roots, giving the final separated group
word contradiction.

The remaining gate is therefore the same genuinely tracial-matrix issue
identified in the eight-lamp spin reduction: recover a nested pair of
commutants in compatible finite coordinates.  The present atlas version has
an additional advantage—`e` is a canonical projection of trace exactly
one half inside the larger commutant.

## 4. What this does not prove

The projection `(RSC4)` is an ambient spectral projection, so it cannot by
itself satisfy a universal one-way leakage identity.  The left regular
representation of the atlas group lies in a finite von Neumann algebra and
realizes `(RSC2)--(RSC9)` exactly.  Abstract finite-von-Neumann-algebra
finiteness therefore cannot force `C=D`; proper finite-index or
self-similar commutant inclusions can exist.

Nor does `(RSC4)` equal the characteristic-two cylinder projection `p_11`.
It removes the positive-density and canonicity problems for a carrier cut,
but the hard pair and comb must still connect that carrier to the two child
arrows in a finite multiplicity algebra.

Two endpoints are now cleanly separated:

1. **Compatible commutant recovery:** recover `(RSC8)` in finite matrix
   coordinates and collapse it by dimension.
2. **Spectral-carrier child recovery:** use the trace-half projection `e`
   as the common finite coefficient carrier, and recover two orthogonal
   child transports from the hard/comb packet.

Either endpoint would finish the atlas nonhyperlinearity proof.  Neither is
currently established.

## 5. Formal status

The load-bearing ring identities now formalized are:

```text
rawInvolutionMatrix_sq
rawInvolutionMatrix_ne_one
rawInvolutionWord_sq
rawInvolutionWord_ne_one
rawInvolutionWord_commutes_compressed_core
```

The complex tracial cut is also kernel-checked in
`GroupApproximation/Sofic/ExactInvolutionCut.lean`:

```text
exactInvolutionNegativeCut_isOrthogonalProjection
normTrace_exactInvolutionNegativeCut
```

Thus both assertions in `(RSC5)`—idempotent self-adjointness and normalized
trace `1/2`—are formal consequences of the exact involution and trace-zero
hypotheses.  The existing approximate involution-rounding infrastructure in
`GroupApproximation/Sofic/ApproxInvolutionCorner.lean` remains available
after the matrix-coordinate recovery theorem is supplied.
