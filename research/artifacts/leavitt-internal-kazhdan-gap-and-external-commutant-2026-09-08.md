# The native Kazhdan gap and the external commutant distinction

2026-09-08. Written group and von Neumann algebra arguments; no new
Lean verification is claimed. This note does not determine
hyperlinearity of the binary Leavitt unit group.

Let \(R=L_{\mathbb F_2}(1,2)\) and identify

\[
H=R^\times\cong GL_4(R)=EL_4(R).
\]

Inside these four coordinates, let

\[
L=\{\operatorname{diag}(A,1):A\in EL_3(R)\},\qquad
K=\{\operatorname{diag}(I_3,k):k\in R^\times\}.
\]

Both groups are copies of \(H\), are finitely generated, and have
property \((T)\). They commute. The ring/group identifications and
simplicity are the established inputs used by
[the full-character theorem](leavitt-full-character-classification-2026-09-08.md).
The native compressor is the unit \(u\) from the manuscript's
rank-four compression cell: \(uLu^{-1}\leq L\), and conjugating
an element of \(K\) produces an element of \(L\) that centralizes
\(uLu^{-1}\) without centralizing \(L\).

Put \(N=L(H)\), \(A=L(L)\), and \(B=L(K)\), with their
canonical traces. The available strong conclusions are

\[
A'\cap N=B,\qquad B'\cap N=A,
\tag{1}
\]

and, in the internal tracial ultrapower,

\[
A'\cap N^\omega=B^\omega,\qquad
B'\cap N^\omega=A^\omega.
\tag{2}
\]

Here the left-hand algebras \(A,B\) are embedded as constant
sequences in \(N^\omega\). Equations (1)--(2) do not identify
commutants in an arbitrary external tracial extension of \(N\).

## 1. The two native group centralizers

We have

\[
C_H(L)=K,\qquad C_H(K)=L.
\tag{3}
\]

For the first equality, write a matrix commuting with \(L\) in
\(3+1\) block form. Commutation with all constant elementary
matrices on the first three coordinates kills the two off-diagonal
blocks and makes the upper block \(aI_3\). Commutation with
\(x_{ij}(r)\) for every \(r\in R\) then gives \(ar=ra\).
The center of \(R\) is \(\mathbb F_2\); invertibility forces
\(a=1\). The lower block is an arbitrary unit, giving \(K\).

For the other equality, write a matrix as
\(\begin{psmallmatrix}A&b\\c&d\end{psmallmatrix}\).
There is a unit \(q\in R\) for which \(q-1\) is also a unit:
use the constant order-three matrix
\(\begin{psmallmatrix}0&1\\1&1\end{psmallmatrix}\) under
\(R\cong M_2(R)\). Commutation with
\(\operatorname{diag}(I_3,q)\) gives
\(b(q-1)=0\) and \((q-1)c=0\), hence \(b=c=0\).
The lower diagonal block is consequently a unit centralizing
\(R^\times\). The center of that infinite simple group is
trivial, so \(d=1\). The upper block belongs to
\(GL_3(R)=EL_3(R)\), giving \(L\).

## 2. Fourier coefficients identify the internal commutants

An infinite simple group has no nontrivial action on a finite set.
Therefore any finite orbit of \(L\) acting on \(H\) by
conjugation is a singleton; by (3), those singletons are exactly
the elements of \(K\).

A vector in \(L^2(N)\cong\ell^2(H)\) fixed by conjugation by
\(L\) has Fourier coefficients constant on every such orbit.
Square summability forces the coefficient on each infinite orbit
to vanish. Its support is therefore contained in \(K\), and
conversely every vector supported on \(K\) is fixed. Thus

\[
L^2(N)^{\operatorname{Ad}L}=L^2(B).
\tag{4}
\]

Intersect with the bounded elements of \(N\) to obtain the
first equality in (1). Exchanging \(L,K\) proves the second.
The invariant-space projection in (4) is the conditional expectation
\(E_B:L^2(N)\to L^2(B)\).

## 3. The exact spectral-gap inequality and internal ultrapower

Let \((S_L,\kappa_L)\) be a Kazhdan pair for \(L\), with
\(S_L\) finite. Apply the defining spectral-gap inequality to
the conjugation representation of \(L\) on \(L^2(N)\) and
its orthogonal complement to (4). For every \(x\in L^2(N)\),

\[
\boxed{
\|x-E_Bx\|_2\leq\kappa_L^{-1}
 \max_{s\in S_L}\|\lambda_sx-x\lambda_s\|_2.}
\tag{5}
\]

In particular this applies to every operator-norm-bounded vector,
with the same constant. There is a reciprocal inequality using a
Kazhdan pair for \(K\) and \(E_A\).

If a bounded sequence \((x_n)\) in \(N\) represents an element
of \(A'\cap N^\omega\), its commutators with \(S_L\) vanish
along \(\omega\). Equation (5) implies
\(\|x_n-E_Bx_n\|_2\to_\omega0\). Conditional expectation
preserves the operator-norm bound, so the same ultrapower element
belongs to \(B^\omega\). The reverse inclusion follows from
commutation. This proves (2).

For an external trace-preserving embedding \(\pi:N\to M\),
property \((T)\) still gives a spectral-gap inequality on
\(L^2(M)\), but its invariant-space projection is

\[
E_{\pi(A)'\cap M},
\tag{6}
\]

not automatically the expectation onto \(\pi(B)\). This is
the distinction relevant to matrix microstates: an embedding into
\(R^\omega\) is an external embedding, not a presentation of
its elements as bounded sequences in the exact factor \(N\).

## 4. An exact H-specific extension with an additional commutant

Consider the amalgamated free product, equivalently the centralizing
HNN extension,

\[
\Gamma=H*_L(L\times\mathbb Z)
=\langle H,z\mid [z,\ell]=1\text{ for every }\ell\in L\rangle.
\tag{7}
\]

The normal form theorem embeds \(H\) in \(\Gamma\), so its
native \(L,K,u\) and every compressor identity remain unchanged.
In the finite tracial algebra \(M=L(\Gamma)\), the restricted
character of \(H\) is its canonical character. Moreover,
\(z\) commutes with \(L\), and

\[
\langle K,z\rangle\cong K*\mathbb Z.
\tag{8}
\]

To check (8), note \(K\cap L=1\). A reduced alternating word
of nonidentity elements of \(K\) and nonzero powers of \(z\)
is a reduced word in the amalgam (7), hence is nonidentity.
Consequently

\[
\pi(A)'\cap M\supset L(K*\mathbb Z)\supsetneqq\pi(B).
\tag{9}
\]

In fact the additional commutant cannot be attributed to an ambient
commutant of all of \(H\), because

\[
C_\Gamma(H)=1,\qquad \pi(N)'\cap M=\mathbb C.
\tag{10}
\]

For the group assertion, use the Bass--Serre tree of (7). The group
\(H\) fixes its distinguished vertex \(v\), and this is its
unique fixed vertex. If it fixed another vertex, it would fix the
geodesic between them, and therefore an edge adjacent to \(v\).
Every edge stabilizer adjacent to \(v\) is a conjugate \(hLh^{-1}\)
with \(h\in H\), a proper subgroup of \(H\). Such an edge
cannot be fixed by all of \(H\). Properness follows, for example,
from the nontrivial fourth-coordinate subgroup \(K\), with
\(L\cap K=1\).

An element of \(\Gamma\) centralizing \(H\) sends \(v\) to
another \(H\)-fixed vertex. Uniqueness makes it stabilize \(v\),
so it belongs to \(H\), and hence to \(Z(H)=1\). This proves
the first assertion of (10). Infinite simplicity of \(H\) again
makes every finite \(H\)-conjugacy orbit in \(\Gamma\) a
singleton. The Fourier argument of Section 2, now on \(\ell^2(\Gamma)\),
then proves the second assertion of (10).

Thus this extension also refutes the stronger proposed identification

\[
\pi(A)'\cap M
\stackrel{?}{=}
\pi(B)\vee(\pi(N)'\cap M),
\tag{11}
\]

while retaining the two native commuting Kazhdan copies, the complete
character information on \(H\), and its native compressor.

## 5. Scope of the remaining compression question

There is no claim that \(L(\Gamma)\) in Section 4 embeds into
\(R^\omega\). It is an exact finite-trace countermodel to
deriving (11) from just the displayed group structure, character
information, and property \((T)\).

To use (5) with the native \(K\)-algebra in external matrix
approximants, one needs an additional identification or controlled
replacement of the actual invariant space (6). Proving such a
statement specifically for the relevant embeddings into
\(R^\omega\) would be new matrix-approximation input. This note
does not claim that even that identification alone would complete
the compressor's finite-dimensional rank comparison: the separate
control of low-spectrum rank and concentration would still need
to be proved at the scope used by the argument.

The recent ultraproduct rigidity theorem does not supply this step.
[Peterson, Theorem 5.2](https://arxiv.org/html/2605.16669v1#S5)
gives an ambient unitary implementing coordinate automorphisms on a
property-(T) subfactor, under a factorial relative-commutant assumption.
For the native coordinate conjugations \(\operatorname{Ad}(U_n)\),
the ultraproduct of the \(U_n\) already implements that action.
The conclusion places no implementing unitary inside the compressed
source factor and supplies no finite-matrix rank comparison. This is
an applicability check, not a counterexample to Peterson's theorem.

## 6. Both relevant native inclusions have infinite index

Put \(\alpha=\operatorname{Ad}(\lambda_u)|_A\) and
\(S=A\vee B\subset N\). The commuting groups \(L,K\) have
trivial intersection, so the canonical trace gives
\(S\cong A\bar\otimes B\). Then

\[
[A:\alpha(A)]=\infty,\qquad [N:S]=\infty.
\tag{12}
\]

For the first statement, write \(p=st\), \(e=1-p\). On the
first three coordinates, \(uLu^{-1}\) acts on the \(p\)-corner
and fixes the complementary \(e\)-corner. The latter corner has
an infinite unit subgroup \(J\), since \(eRe\cong R\).
Its support is orthogonal to that of the compressed copy, so
\(J\cap uLu^{-1}=1\). The elements of \(J\) therefore give
infinitely many distinct cosets of \(uLu^{-1}\) in \(L\),
and their group unitaries form an infinite orthonormal family as
a right \(\alpha(A)\)-module. In particular \(\alpha(A)\)
is a proper subfactor of \(A\), and every \(\alpha^n(A)\)
with \(n>0\) is proper.

For the second statement, we prove

\[
E_S(\lambda_u^n)=0\quad(n\ne0).
\tag{13}
\]

Suppose \(n>0\) and \(T=E_S(\lambda_u^n)\ne0\).
Bimodularity of conditional expectation gives
\(Tx=\alpha^n(x)T\) for \(x\in A\). A nonzero normal
slice of \(T\in A\bar\otimes B\) gives \(a\in A\setminus\{0\}\)
with \(ax=\alpha^n(x)a\). Hence \(a^*a\) is a nonzero
scalar, because \(A\) is a factor. Its polar part is an isometry
in the finite factor \(A\), hence a unitary. The intertwining
identity would then imply \(\alpha^n(A)=A\), a contradiction.
Negative \(n\) follow by taking adjoints. Equation (13) makes
\(1,\lambda_u,\lambda_u^2,\ldots\) an orthonormal family of
right \(S\)-module vectors, proving \([N:S]=\infty\).

These are assertions about the exact native group factor, independent
of embeddability. Applying finite-index rigidity to these inclusions
would require an additional hypothesis that is absent here.
