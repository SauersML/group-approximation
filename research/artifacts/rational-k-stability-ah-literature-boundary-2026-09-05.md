# Rational K-stability versus K-stability for AH algebras: exact target

Date: 5 September 2026. Primary-source audit and scope clarification.
This records an open target; it is not a solution manuscript.

## 1. Published question and conventions

In his contribution to Jaydeb Sarkar's compendium, Prahlad Vaidyanathan
asks whether the equivalence between rational K-stability and K-stability
known for AF and AT algebras extends to AH algebras. His wording does
not impose simplicity or unitality. See
[Section 20, printed page 48](https://www.isibang.ac.in/~jay/papers/oaotINSA.pdf).
The simple unital version is therefore a narrower research target,
not a verbatim statement of a separately numbered problem.

Here AH means an inductive limit of finite sums of homogeneous algebras
\(pC(X,M_n)p\) with compact spectra \(X\). Connecting maps need not
be unital. The simple unital target allows nontrivial vector bundles
and twisted connecting maps.

Use the conventions of
[Seth--Vaidyanathan, Definitions 1.1 and 1.3](https://arxiv.org/pdf/2102.13529):
integral K-stability requires every adjacent matrix inclusion to induce
an isomorphism on all \(\pi_k\), \(k\ge0\), of the quasi-unitary group.
Rational K-stability requires this after tensoring with \(\mathbb Q\)
in positive degrees only. It does not impose a rationalized degree-zero
condition. For unital algebras these are the usual unitary groups.

## 2. Settled boundaries

For every AT algebra, rational K-stability, K-stability, and slow
dimension growth are equivalent:
[Seth--Vaidyanathan, Theorem A](https://arxiv.org/pdf/2203.00979).

The unrestricted converse already fails. Example 2.1 of
[the rational continuous-fields paper](https://arxiv.org/pdf/2102.13529)
uses \(C_*(\mathbb{RP}^2,\mathbb C)\), the functions vanishing at a
chosen point. Its rational nonstable groups vanish, while integral
stability fails. Thus a new example must address the AH restriction,
not merely separate the two notions for arbitrary C*-algebras.

Every simple unital infinite-dimensional diagonal AH algebra, in
the globally trivial matrix-bundle convention of Seth's paper,
is K-stable even after tensoring with any C*-algebra:
[Corollary 3.10](https://arxiv.org/pdf/2512.04780).
Consequently ordinary diagonal matrix-function towers cannot supply
a counterexample in that class. Twisted homogeneous bundles require
a separate analysis.

## 3. Why the pointed example does not settle the compact-block target

Write \(Y=\mathbb{RP}^2\setminus\{x_0\}\). This space is connected
and noncompact. Any projection in \(M_n(C_0(Y))\) has locally constant
rank, hence constant rank. Vanishing at infinity forces that rank to
be zero. Thus all these matrix algebras have no nonzero projections.

Every homomorphism from a unital C*-algebra into \(C_0(Y)\) is zero:
the image of its unit would be a projection, and its vanishing forces
the homomorphism to vanish. Canonical maps from compact homogeneous
building blocks into a proposed AH limit would therefore all vanish.
Their images cannot have dense union in the nonzero algebra \(C_0(Y)\).
This proves the example is outside the convention in Section 1,
even though it is homogeneous over a locally compact spectrum.

Unitization does not repair this. Constants and evaluation split
\(U(M_n(C(\mathbb{RP}^2)))\to U(n)\), naturally in \(n\).
Since \(\pi_3U(1)\otimes\mathbb Q=0\) while
\(\pi_3U(2)\otimes\mathbb Q=\mathbb Q\), the matrix inclusion
at sizes one and two fails rational surjectivity on the constant
summand. Hence the unitization is not rationally K-stable.

## 4. Current construction boundary

Our [persistent Euler towers](stw59-persistent-euler-degree-one-cokernel-2026-09-05.md)
have
\[
 \operatorname{coker}\bigl(\pi_1U(A)\longrightarrow K_0(A)\bigr)
 \cong\mathbb Z^s,\qquad s\ge1.
\]
Their matrix algebras of size at least two are K-stable. Exactness of
rationalization therefore shows these towers fail rational K-stability.
This remains true when their degree-zero obstruction is finite torsion
or zero. Torsion in one computed unstable group does not by itself
establish rational K-stability in all positive degrees.

A possible next construction would retain an integral torsion
obstruction on rationally acyclic finite bases. It must prove both
survival under the actual simplicity-producing connecting maps and
rational stability in every fixed positive degree. No such tower
is established in this audit. In particular, checking only Chern
characters or line-bundle-generated K-classes would leave possible
integral torsion contributions uncontrolled.

The checked primary sources do not settle the general compact-block
AH question or its simple unital twisted-bundle specialization.
This is a statement about the sources inspected, not an exhaustive
priority or novelty certification.
