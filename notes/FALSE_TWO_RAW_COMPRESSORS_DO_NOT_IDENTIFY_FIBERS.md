# Two raw compressors do not by themselves identify extension fibers

Date: 2026-08-13

## Outcome

The raw two-compressor packet has the correct infinite-index geometry, but
its common covariance relation does **not** provide two independent
coefficient columns.  The second compressor differs from the first by a
unitary in the centralizer of the compressed core.  At finite matrix
coordinates this remains true quantitatively, with no dimension loss.

Consequently the proposed Pauli extraction cannot infer a binary Leavitt
family, cross-orthogonal columns, or the one-cut leakage asymmetry from the
two compressor covariance equations alone.  A successful proof must use a
named adjacent-root relation which detects the resulting centralizer
holonomy.

## 1. Exact algebra

In `Leavitt/RawSwapCompressors.lean`, write

```text
u = compressor L,
w = rawInvolutionWord L,
v = rawSecondCompressor L = w u.
```

Both `u` and `v` implement the same injective corner endomorphism `alpha` on
the embedded rank-three core:

```text
u g u^(-1) = alpha(g),
v g v^(-1) = alpha(g).
```

It follows identically that

```text
w = v u^(-1) in C(alpha(Core)).
```

This is already proved concretely by
`rawInvolutionWord_commutes_compressed_core`.  Thus `w` acts inside the
multiplicity spaces of the compressed-core isotypic decomposition.  It does
not create a second copy of the source representation.

In characteristic two its displayed nontrivial block is

```text
[ p0  s1 ]
[ t1   0 ],
```

an involution.  In the genuine Leavitt module it fixes the `p0` part of the
first coordinate and swaps the `p1` part with the whole second coordinate.
This is exactly the infinite-multiplicity index geometry one wants to rule
out.  But the projections `p0,p1` are entries of a preferred ring-matrix
model; they are not intrinsic spectral projections of an arbitrary group
microstate.

## 2. Dimension-free matrix identity

Let `U,V,A,B` be square matrices with `U,V` unitary.  Put

```text
E_U = U A U* - B,
E_V = V A V* - B.
```

Direct multiplication gives

```text
((V* U) A - A (V* U)) (U* V)
  = V* (E_U-E_V) V.
```

Unitary invariance of normalized Hilbert--Schmidt norm therefore yields the
exact equality

```text
||(V* U) A - A (V* U)||_2^2 = ||E_U-E_V||_2^2.
```

In particular, two `delta`-covariances make their relative implementer an
`O(delta)` approximate centralizer, uniformly in dimension.  The identity is
formalized in
`Sofic/RelativeImplementerCentralizer.lean` as
`hsNormSq_relativeImplementer_commutator`.

Applied to the atlas, the two raw compressor matrices therefore give one
transport from a source character block to the full sum of its extension
fibers, followed by an internal unitary on that extension sum.  Treating the
two transports as columns of one isometry silently assumes their cross
orthogonality, which is precisely the missing Leavitt coefficient relation.

## 3. Consequence for the active endpoint

The following inference is invalid:

```text
two compressor unitaries implementing alpha
  => two isometric coefficient columns
  => a 2:1 Hall deficit.
```

What the relations actually give is

```text
one compressor transport
  + centralizer-valued fiber holonomy.
```

The finite Pauli/Clifford packet does not repair this: a finite Clifford
normalizer can realize such holonomy exactly on the Pauli factor, while an
arbitrary unitary remains on the multiplicity factor.

The smallest still-live atlas statement is therefore sharper than “use both
raw compressors.”  One must exhibit a fixed adjacent-root word `r` for which
the Pauli coefficient of

```text
w r w^(-1)
```

acts between two different extension-fiber summands and cannot be absorbed
by the compressed-core commutant gauge.  Equivalently, a closed word in the
finite chart/Pauli groupoid must have nontrivial multiplicity holonomy whose
one-way leakage is bounded below independently of the chart multiplicity.

Until such a word is identified, `(RPC47)`, `(RPC116)`, and `(RPC128)` remain
conditional extraction gates rather than consequences of the printed raw
compressor matrices.

## 4. Research decision

Do not spend further time expanding the two covariance equations or their
central-root Fourier support graphs.  Those equations are now completely
accounted for by the relative-centralizer identity above.  The next atlas
calculation must include:

1. one adjacent noncentral root moved by `w`;
2. one compressor transport fixing the source-to-extension map; and
3. a return path to the original Pauli sector.

Only the resulting closed holonomy is gauge invariant.  If every shortest
such loop acts by a finite Clifford automorphism, the raw-compressor atlas
route is locally sterile and the search must move to a different global
relation or to the perfect-completeness program.

## 5. The shortest adjacent-root square is sterile

The two explicit mul-past identities in `RawSwapCompressors.lean` are, for
indices away from coordinate zero,

```text
w x_0j(s1 a) w^(-1) = x_4j(-a),
w x_i0(b t1) w^(-1) = x_i4(-b).
```

Take distinct `i,j` and orient the roots so the ordinary Steinberg
commutator applies.  The commutator before conjugation contains

```text
(b t1)(s1 a) = ba,
```

while the commutator after conjugation contains `(-b)(-a)=ba`.  Thus the
closed square records exactly `t1 s1=1`.

This still does not detect multiplicity holonomy.  On a nontrivial central
character sector the source and target finite Heisenberg representations
are copies of the same unique irreducible representation.  Stone--von
Neumann uniqueness therefore writes every intertwiner as

```text
S_fixed tensor C,
```

where `S_fixed` is the forced Pauli intertwiner and `C` is an arbitrary
unitary on the multiplicity space.  Going around the commutator square
cancels `S_fixed`; the coefficient `C` and its inverse cancel as well.  The
loop is consequently satisfied for every multiplicity holonomy.

This closes the shortest candidate loop without computation.  A useful loop
must compare **two inequivalent paths between the same fiber sums**, not a
path and its conjugate.  In coefficient language it must use both corner
branches and a cross identity such as `t0 s1=0`; a diagonal identity such as
`t1 s1=1` only verifies that one transport is invertible.

## 6. Collision word 19243 is a parent-block identity

The fixed radius-five collision-tree word at index `19243` was reconstructed
exactly by `experiments/atlas_decode_collision_words.py`.  Put

```text
X = p2_01,   Y = p2_10,   Q = p1_23.
```

Then the word is

```text
r19243 = (Y X) Q Y Q (X Y) Q X Q.                    (RCH1)
```

It has length eight, and both of its free-factor projections are the
identity.  Since `X^2=Y^2=Q^2=1` and `(XY)^3=1`, it may equivalently be
written as the closed conjugacy product

```text
((Y X) Q (Y X)^-1)
((Y X Y) Q (Y X Y)^-1)
(X Q X^-1)
Q.                                                     (RCH2)
```

In the prefix realization the first-chart transvection `Q` shears the
sibling leaves `001` and `000` inside the parent cylinder `00`, whereas
`X,Y` act on the second-chart pair `00,1`.  This initially looks like the
desired child-versus-parent refinement loop.  However, relative to the
parent decomposition `00 + 1`, the three units have the two-by-two form

```text
X = [1 1]    Y = [1 0]    Q = [K 0]
    [0 1],       [1 1],       [0 1],
```

where `K` is merely an involution.  No properness information about the
child support of `K` remains.  Direct multiplication in every
characteristic-two ring gives

```text
(Y X) Q Y Q (X Y) Q X Q = I                         (RCH3)
```

from the single equation `K^2=1`.  This generic identity is formalized in
`Leavitt/Collision19243.lean` as
`collision19243_parentBlock_identity`.

The exact reconstruction is stored in `experiments/atlas-word-19243.json`.
It explains why this word kills the previously audited affine and natural
alternating-group alignments: their classical fold does not preserve the
required parent block, so the value becomes a noncentral involution.  But an
arbitrary tracial matrix model can realize `(RCH3)` in a finite parent block
without seeing that `K` came from a proper child.  Thus word `19243` is not
the missing gauge-invariant cross-coefficient loop and cannot by itself
force `t0 s1=0` or one-way leakage.

This closes the shortest global collision candidate as well as the shortest
local adjacent-root square.  A live word must retain **two distinct child
branches after parent-block compression**.  Any word whose raw block
reduction uses only a single involution `K` is automatically too coarse.

## 7. The surviving two-branch packet

The decoder also reconstructs the two hard boundary representatives at
boundary indices `11` and `30`; see
`experiments/atlas-boundary-11-30.json`.  Both have length eight and are
exact Leavitt identities.  Their hard running-prefix/next-letter pairs are
the six pairs audited in `FALSE_ATLAS_INFINITE_PROJECTION.md`.  Unlike word
`19243`, each such pair generates both child cylinder projections and a
partial isometry from a cylinder onto one proper child.

This does not yet transfer to an arbitrary unitary group microstate.  The
projection identities are additive identities over `F_2`, while the group
relations initially supply only root involutions and their Weyl pairings.
The exact finite endpoint is already proved by
`two_sub_sqrt_three_le_max_unitary_pairing_defects`: four contraction arrows
on one flat pairing space cannot satisfy the two diagonal products and one
cross product.  The sole live atlas implication is therefore:

```text
hard two-branch prefix packet + raw compressor covariance
  => one common reduced Fourier multiplicity space
  => the four radical-quotient arrows on that space.
```

The first arrow is the remaining matrix-specific extraction theorem.  The
relative-centralizer lemma and `(RCH3)` show exactly what it must retain:
two child labels, not two implementations of one parent transport and not
one abstract involution in the parent block.
