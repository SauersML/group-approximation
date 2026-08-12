# The positive compressor semigroup is not Ore

Date: 2026-08-12

## 1. Outcome

For the explicit monomial-cone Kun--Thom pair, the simultaneous dilation in
`FALSE_FULL_COMPRESSION_SEMIGROUP_DILATION.md` cannot be converted into an
ordinary group dilation by an Ore-semigroup theorem.

More precisely, let

\[
 \Lambda=M_{3\times2}(\mathbf Z),\qquad
 \Lambda_+=M_{3\times2}(\mathbf N),
\]

let (L=\operatorname{SL}_3(\mathbf Z)) act on both columns by left
multiplication, and put

\[
 R_+=A[\Lambda_+]\subset R=A[\Lambda],\qquad
 \Gamma=E_r(R_+),\qquad
 G=E_r(R)\rtimes L.
 \tag{ONO1}
\]

Here (A) may be the square-zero coefficient ring used in the framed pair,
or simply (mathbf Z).  If

\[
 S=P_\Gamma=\{s\in G:s\Gamma s^{-1}\leq\Gamma\},
 \tag{ONO2}
\]

then (S) is neither right Ore nor left Ore.  In fact, it contains two
elements which have neither a common right multiple nor a common left
multiple in (S).  Consequently (S) has no right- or left-cofinal Ore
subsemigroup.

The obstruction occurs entirely in the external positive matrix monoid.  It
is dimension-free and does not depend on Connes embeddability.

## 2. Every compressor has a positive external component

Let (s=(g,\ell)\in S), with (g\in E_r(R)) and 
(ell\in L).  For (a\in R_+) and (i\neq j), compressor containment
gives

\[
 g\bigl(1+(\ell a)e_{ij}\bigr)g^{-1}\in E_r(R_+).
 \tag{ONO3}
\]

Subtracting the identity shows

\[
 \operatorname{Ad}_g((\ell a)e_{ij})\in M_r(R_+).
 \tag{ONO4}
\]

Taking (a=1) also gives

\[
 \operatorname{Ad}_g(e_{ji})\in M_r(R_+).
 \tag{ONO5}
\]

Multiplying `(ONO4)` and `(ONO5)`, and doing this for every diagonal
coordinate, yields

\[
 \operatorname{Ad}_g((\ell a)e_{ii})\in M_r(R_+)
 \quad\text{for every }i.
 \tag{ONO6}
\]

After summing over (i), the inner conjugation disappears on the scalar
matrix:

\[
 (\ell a)I_r
 =\operatorname{Ad}_g((\ell a)I_r)\in M_r(R_+).
 \tag{ONO7}
\]

Thus

\[
 \ell(R_+)\subseteq R_+.
 \tag{ONO8}
\]

Apply this to the group-ring basis monomials.  Since those monomials are
linearly independent over (A), `(ONO8)` implies

\[
 \ell(\Lambda_+)\subseteq\Lambda_+.
 \tag{ONO9}
\]

For the left action on two copies of (mathbf Z^3), `(ONO9)` is equivalent
to all entries of (ell) being nonnegative.  Hence the external projection
of (S) lies in

\[
 L_+=\operatorname{SL}_3(\mathbf Z)\cap M_3(\mathbf N).
 \tag{ONO10}
\]

Conversely, every element of (L_+) preserves (Lambda_+), so its copy
inside (G) belongs to (S).  Therefore the external projection of (S)
is exactly (L_+).

## 3. Two positive transvections have no common right multiple

Take

\[
 A=I+e_{12},\qquad B=I+e_{21}\in L_+\subseteq S.
 \tag{ONO11}
\]

Their positive column cones are

\[
 A\mathbf R_+^3
 =\{x\in\mathbf R_+^3:x_1\geq x_2\},
\]

and

\[
 B\mathbf R_+^3
 =\{x\in\mathbf R_+^3:x_2\geq x_1\}.
 \tag{ONO12}
\]

Consequently

\[
 A\mathbf R_+^3\cap B\mathbf R_+^3
 =\{x\in\mathbf R_+^3:x_1=x_2\},
 \tag{ONO13}
\]

which spans a two-dimensional subspace.

If (AX=BY=C) for (X,Y\in L_+), then every column of (C) belongs to
the intersection `(ONO13)`.  Hence (operatorname{rank}(C)\leq2), which
contradicts (det(C)=1).  Thus (A) and (B) have no common right
multiple in (L_+).

If they had a common right multiple in (S), projecting to (L_+) would
give one in (L_+).  Therefore they have no common right multiple in
(S), and (S) is not right Ore.

## 4. The left-Ore and cofinal variants also fail

Suppose (XA=YB) with (X,Y\in L_+).  Transposition gives

\[
 A^{\mathsf T}X^{\mathsf T}=B^{\mathsf T}Y^{\mathsf T}.
 \tag{ONO14}
\]

But (A^{\mathsf T}=B), (B^{\mathsf T}=A), and transposition preserves
(L_+).  Equation `(ONO14)` would therefore be a common right multiple of
(A) and (B), already ruled out.  Projection from (S) again proves
that no common left multiple exists in (S).  Thus (S) is not left Ore.

There is no cofinal workaround.  For example, if (T\subseteq S) were
right cofinal in the sense that every (s\in S) has a right multiple in
(T), choose

\[
 Ax\in T,\qquad By\in T.
\]

If (T) were right Ore, these two elements would have a common right
multiple, which would also be a common right multiple of (A) and (B)
in (S).  This is impossible.  The left-cofinal case is identical.

## 5. Consequence for the main construction

The one-variable dilation theorem works because the powers of a single
compressor form a directed semigroup.  The full positive system has genuine
branching already at the two elementary transvections `(ONO11)`.  The
branching cannot be removed by passing to a cofinal Ore subsystem.

Accordingly, the simultaneous CE problem in
`FALSE_FULL_COMPRESSION_SEMIGROUP_DILATION.md` is not an omitted application
of a standard Ore dilation theorem.  Any successful construction must use
the non-Ore branching itself--for example by a finite-matrix correspondence
or product-system model--rather than replacing it by an ordinary inductive
limit indexed by a group of fractions.
