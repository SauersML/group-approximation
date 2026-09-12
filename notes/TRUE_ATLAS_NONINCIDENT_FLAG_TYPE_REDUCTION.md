# The atlas overlap has one two-dimensional spherical gauge block

Date: 2026-08-13

## 1. Exact outcome

Let

\[
 G=\operatorname{GL}_4(\mathbf F_2)\cong A_8,
 \qquad
 H=\left\{\begin{pmatrix}A&0\\0&1\end{pmatrix}:A\in
 \operatorname{GL}_3(\mathbf F_2)\right\}.
 \tag{NFG1}
\]

The overlap used by the Leavitt atlas is not an abstract index-120
subgroup.  It is the stabilizer of the nonincident flag

\[
 (\langle e_4\rangle,\ker e_4^*).
 \tag{NFG2}
\]

There are 15 points and 15 hyperplanes in
`PG(3,2)`.  Every point is outside exactly eight hyperplanes, so there are

\[
 15\cdot 8=120=[G:H]
 \tag{NFG3}
\]

nonincident point--hyperplane flags.  Thus

\[
 \mathbf C[G/H]
 \cong \mathbf C[\{(p,L):p\notin L\}].
 \tag{NFG4}
\]

The exact ordinary-character decomposition is

\[
 \boxed{
 \operatorname{Ind}_H^G(1)
   \cong 1\oplus 14^{\oplus2}\oplus35\oplus56.}
 \tag{NFG5}
\]

The point and hyperplane permutation modules both decompose as

\[
 \operatorname{Ind}_{M_p}^G(1)
 \cong \operatorname{Ind}_{M_L}^G(1)
 \cong1\oplus14.
 \tag{NFG6}
\]

Consequently the spherical commutant has dimension

\[
 \dim\operatorname{End}_G\mathbf C[G/H]
 =1^2+2^2+1^2+1^2=7.
 \tag{NFG7}
\]

In particular, the overlap module is almost multiplicity-free.  Its only
non-scalar representation-type gauge is one `2 x 2` block, on the two
copies of the 14-dimensional constituent.  The 35- and 56-dimensional
spherical types have scalar gauge.

This is an exact reduction of the finite-multiplicity recovery problem.  It
does not yet prove that the raw-compressor packet acts inside this spherical
module, which is the remaining functoriality gate.

## 2. Where the repeated 14 comes from

Let `X` be the 15 points and `Y` the 15 hyperplanes.  The two coordinate
maps from the nonincident-flag set

\[
 \Omega=\{(x,y)\in X\times Y:x\notin y\}
 \tag{NFG8}
\]

give normalized pullback isometries

\[
 J_X:\ell^2(X)\longrightarrow\ell^2(\Omega),
 \qquad
 J_Y:\ell^2(Y)\longrightarrow\ell^2(\Omega).
 \tag{NFG9}
\]

Their cross Gram operator is `B/8`, where

\[
 B_{x,y}=1_{x\notin y}.
 \tag{NFG10}
\]

After identifying points and hyperplanes by the standard polarity, exact
counting gives

\[
 BB^*=4I+4J.
 \tag{NFG11}
\]

Indeed, a row has eight ones, while two distinct points are simultaneously
outside four hyperplanes.  Hence `B/8` has singular value one on constants
and singular value `1/4` on the 14-dimensional zero-sum constituent.
The two 15-dimensional pullback modules intersect precisely in the constant
line and span

\[
 1\oplus14^{\oplus2}.
 \tag{NFG12}
\]

The orthogonal complement is exactly

\[
 35\oplus56.
 \tag{NFG13}
\]

Thus the two natural point/hyperplane coordinate systems do not canonically
identify the desired child coefficient: they leave a genuine two-dimensional
multiplicity rotation.  But there is no larger unidentified spherical
matrix block.

## 3. Positive-density interpretation in a regular chart

For one regular chart

\[
 \lambda_G\otimes1_k,
 \tag{NFG14}
\]

the right-`H`-fixed subspace has dimension `120k`, a fixed fraction
`1/168` of the chart.  Its four spherical pieces have dimensions

\[
 k,\quad28k,\quad35k,\quad56k.
 \tag{NFG15}
\]

Therefore none of the nontrivial pieces disappears as the regular
multiplicity grows.  In particular, the multiplicity-one 35 and 56 sectors
are positive-density scalar test channels, while every ambiguity in the
point/hyperplane sector is confined to `U(2)` on the 14-doublet.

The qualification "right-`H`-fixed" matters.  A right regular action is a
choice in the commutant of the left regular chart.  Changing the regular
chart gauge changes that choice.  Consequently `(NFG5)` is not by itself a
canonical ambient spectral decomposition in `L(Q)` and does not contradict
the exact Leavitt representation.  A valid use must show that the
boundary-plus-raw-compressor packet selects the corresponding spherical
module, or else formulate a statement invariant under its remaining
commutant gauge.

## 4. Revised finite calculation

The first version of this section proposed a direct scalar spherical test.
That test has now been run and falsified exactly.  The compiled raw swap and
comb reduce to the identity in the classical amalgam `A8 *_H A8`, and the
hard class-11 pair reduces into `H`.  Thus no constituent in `(NFG5)` sees a
nontrivial zeroth-order holonomy.  The decomposition remains the exact gauge
atlas for any later recovered edge module, but it cannot itself recover the
transverse coefficient corner.  See
`FALSE_CLASSICAL_SPHERICAL_RAW_PACKET_COLLAPSE.md`.

For the record, the now-closed proposal split the raw-compressor
projection-recovery problem into two tests.

1. **Scalar spherical test.**  Project the hard pair and the two raw
   compressor transports to the 35 and 56 spherical constituents.  Any
   closed holonomy there is scalar.  A nonzero child-versus-parent index in
   either constituent cannot be absorbed by multiplicity gauge.

2. **14-doublet test.**  If both scalar sectors are balanced, compute the
   induced `2 x 2` holonomy on the two point/hyperplane copies of the 14.
   The only possible hiding place for the missing branch is then a sequence
   of `U(2)` matrices, tensored with the external regular multiplicity.
   The cross Gram value `1/4` in `(NFG11)` fixes the change of frame between
   the two natural bases.

This is sharper than optimizing an arbitrary `15 x 15` natural-module
unitary or an arbitrary `120 x 120` flag unitary.  It also explains why the
15-point module alone could not settle the problem: it sees one copy of the
14, whereas the actual overlap flag module contains two.

The remaining algebraic question is now explicit:

> Do the hard class-11 packet, the raw swap, and the comb compressor descend
> functorially to the right-`H` spherical module, and if so, does their
> properly-infinite two-child class survive in the scalar 35/56 sectors or
> in the fixed `2 x 2` 14-holonomy?

The exact amalgam audit gives this negative answer.  Finite-chart isotypic
decomposition at the aligned fold cannot recover the characteristic-two
coefficient corner.  The atlas program must extract nonlinear coefficient
arrows on the Reynolds-misaligned branch before applying any spherical
decomposition, or return to the full root-pairing or perfect-completeness
endpoint.

## 5. Exact replay

`experiments/atlas_nonincident_flag_character.g` constructs the three
subgroups directly inside `GL(4,2)`, induces their trivial characters, and
computes all scalar products with the fourteen irreducible characters.
It also checks all commutant and intertwiner dimensions.  Run it on MSI with
one core:

```text
module load sagemath/10.7
sage -gap -q experiments/atlas_nonincident_flag_character.g
```

The committed output is
`experiments/atlas-nonincident-flag-character.txt`.

The underlying finite geometry is independently kernel-checked in
`GroupApproximation/Leavitt/NonincidentFlagGram.lean`.  It proves that
`F_2^4` has 15 nonzero projective representatives, that the nonincident flag
set has cardinality 120, and the entrywise Gram identity

```text
sum_h B(p,h) B(q,h) = 8 if p=q, and 4 otherwise.
```

This is the exact combinatorial input for `(NFG11)`; the ordinary-character
decomposition `(NFG5)` remains certified by the GAP replay.
