# A virtually cyclic radical-shear edge

This note improves the centralizer-shear endpoint for the binary Laurent
Kun--Thom double.  The primitive length-two radical word used previously has
a large centralizer: its axis pointwise stabilizer contains a polynomial
elementary subgroup.  A length-four radical word separated by an
opposite-cone substitution has finite axis pointwise stabilizer.  Its full
centralizer is therefore virtually cyclic, so the remaining twisted-lift
problem can be posed over an amenable edge.

The result does **not** prove the twisted double MF.  Shulman's theorem for
an untwisted symmetric double does not automatically cover the twisted edge.
What it removes is all nonamenable centralizer bookkeeping from that last
compatibility problem.

## 1. The opposite-cone substitution

Use the binary Kun--Thom pair with `d=4` and `r>=3`:

\[
 R_+=\mathbb F_2[x_1,x_2,x_3,x_4],\qquad
 R=\mathbb F_2[x_1^{\pm1},x_2^{\pm1},x_3^{\pm1},x_4^{\pm1}],
\]

\[
 \Gamma=\operatorname{EL}_r(R_+),\qquad
 N=\operatorname{EL}_r(R),\qquad
 G=N\rtimes\operatorname{SL}_4(\mathbb Z).
\]

Put `B=I+E_12` in `SL_4(Z)` and `A=-B`.  Then `A` belongs to
`SL_4(Z)`, has infinite order, and is not an involution.  Every entry of
`A` is nonpositive.  Hence

\[
 A(\mathbb N^4)\cap\mathbb N^4=\{0\}
\]

and, for the induced monomial substitution,

\[
 R_+\cap A(R_+)=\mathbb F_2.                         \tag{1}
\]

It follows that

\[
 \Gamma\cap A\Gamma A^{-1}\subseteq
 \operatorname{GL}_r(\mathbb F_2).                   \tag{2}
\]

In particular this intersection is finite.  Indeed, a matrix in the
intersection has all entries both in `R_+` and in `A(R_+)`; (1) makes every
entry constant.

## 2. A radical word with finite axis kernel

Let

\[
 D=G*_{\Gamma}G
\]

and denote the two vertex embeddings by `i_1,i_2`.  Choose

\[
 n=e_{12}(x_1^{-1})\in N\setminus\Gamma,
 \qquad
 \delta=i_2(n)i_1(n)^{-1}.
\]

Embed `A` in the first vertex and put

\[
 w=\delta\,i_1(A)\,\delta\,i_1(A)^{-1}.              \tag{3}
\]

Let

\[
 q:D\longrightarrow G*_{N}G
\]

be the quotient which enlarges the amalgamated subgroup.  Since
`delta` is in `ker(q)`, so is `w`.  The complete-radical calculation for
the symmetric double gives

\[
 w\in\ker(q)\subseteq\operatorname{Rad}_{\rm sof}(D).\tag{4}
\]

Expanding (3) gives the alternating normal form

\[
 i_2(n)\; i_1(n^{-1}A)\; i_2(n)\;i_1(n^{-1}A^{-1}).  \tag{5}
\]

All four syllables lie outside `Gamma`: the first and third because
`n` is not polynomial, and the other two because their
`SL_4(Z)`-coordinates are `A` and `A^{-1}`.  Thus (5) is cyclically
reduced and `w` is hyperbolic of translation length four in the
Bass--Serre tree.

**Theorem (finite axis kernel).**  The pointwise stabilizer of the axis of
`w` is finite.  Consequently `C_D(w)` is finite-by-cyclic and amenable.

**Proof.**  Let `e` be the base edge, whose stabilizer is `Gamma`.  The
axis determined by (5) contains the successive edges represented by the
prefixes

\[
 1,\qquad i_2(n),\qquad \delta i_1(A).
\]

If `k` fixes the axis pointwise, fixing the first two of these edges gives

\[
 k\in\Gamma,\qquad n^{-1}kn\in\Gamma.                \tag{6}
\]

The second condition permits the middle term to be transferred across the
amalgam and gives

\[
 \delta^{-1}k\delta=k.                                \tag{7}
\]

Fixing the third displayed edge now gives

\[
 (\delta i_1(A))^{-1}k(\delta i_1(A))
 =i_1(A)^{-1}ki_1(A)\in\Gamma.                        \tag{8}
\]

Therefore the pointwise axis stabilizer is contained in
`Gamma intersection A Gamma A^{-1}`, which is finite by (2).

Every element centralizing a hyperbolic tree automorphism preserves its
axis and its orientation.  Translation on that axis defines a homomorphism

\[
 \ell:C_D(w)\longrightarrow\mathbb Z
\]

whose kernel is the finite pointwise stabilizer and whose image is cyclic.
This proves the conclusion.  \(\square\)

The use of the length-four word is essential.  For the old word `delta`,
every element of `Gamma intersection n Gamma n^{-1}` commutes with
`delta`; for the displayed root `n`, this contains a large polynomial
elementary block.  The opposite-cone separator in (3) removes that kernel.

## 3. Prime-order central shear

Put `C=C_D(w)`.  The integer `ell(w)` is nonzero.  Choose a prime `p` not
dividing it, introduce a central element `z` of order `p`, and define an
automorphism of `C times <z>` by

\[
 \alpha(cz^j)=c z^{j+\ell(c)}.                        \tag{9}
\]

Here the exponent is read modulo `p`.  Form the twisted double

\[
 J=(D\times C_p)
   *_{(C\times C_p,\,\mathrm{id}),(C\times C_p,\,\alpha)}
   (D\times C_p).                                     \tag{10}
\]

**Proposition (amenable-edge central radical).**  In `J`, the element `z`
is central, nontrivial, and belongs to the full sofic radical.  The
amalgamated edge group `C times C_p` is amenable and virtually cyclic.

**Proof.**  Bass--Serre normal form keeps the two vertex groups injective,
so `z` is nontrivial.  It is central in both vertices and is fixed by
`alpha`, hence is central in `J`.  The edge relation at `w` is

\[
 w_1=w_2 z^{\ell(w)}.                                 \tag{11}
\]

Every homomorphism from `J` to a sofic group kills both `w_1` and `w_2`,
because its restrictions to the two copies of `D` have sofic image and
`w` belongs to `Rad_sof(D)`.  Equation (11) kills `z^{ell(w)}`.  Since
`p` does not divide `ell(w)`, it kills `z`.  The edge is finite-by-cyclic
by the theorem.  \(\square\)

## 4. Exact remaining analytic statement

The group `D` is weak/operator-norm MF by the symmetric-double theorem, so
each vertex `D times C_p` in (10) is weak MF.  If (10) is weak MF, the
central-torsion corner argument produces a tracial-ultraproduct quotient in
which `z` survives.  That quotient is hyperlinear and cannot be sofic,
because every sofic image kills `z`.  Thus weak MF of (10) settles
hyperlinear versus sofic negatively.

Shulman's Theorem 10 proves `A *_C A` is MF for identical edge embeddings.
Her general criterion (Theorem 20) says that (10) is MF exactly when the two
vertex embeddings into a norm matrix corona can be made compatible on the
twisted edge.  The theorem above reduces that compatibility problem from
the nonamenable group `C_D(delta)` to the virtually cyclic group `C_D(w)`.
It does not by itself supply the compatible embeddings.  In the
`z=exp(2 pi i/p)` sector, the only remaining edge datum is a `p`-fold
rotation balance for the spectrum of the cyclic translation generator,
together with its finite axis-kernel type.

This is a genuinely smaller target than the previous balanced-relative-lift
problem: no Kazhdan or polynomial elementary subgroup remains in the edge.

There is an even sharper stabilized variant in `notes/NOTEPAD.md`, theorem
`(FCS1)--(FCS7)`: replacing `D` by `D * Z` turns a commutator of a radical
word with the new free generator into a primitive radical word with exactly
cyclic centralizer.  That variant should be preferred for model production;
the present theorem records that one can already obtain an amenable edge
inside the original double without free stabilization.

Neither variant can be reduced to Shulman's untwisted theorem by extending
the edge shear to a vertex automorphism.  Indeed

\[
 \operatorname{Rad}_{\rm sof}(B\times C_p)
 =\operatorname{Rad}_{\rm sof}(B)\times\{1\}.
\]

The radical is characteristic, so an automorphism of the vertex cannot send
`(w,1)` to `(w,z)`.  The cyclic spectral compatibility is therefore a real
relative-lift problem rather than a presentation artifact.
