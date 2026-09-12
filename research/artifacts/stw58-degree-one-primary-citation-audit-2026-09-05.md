# STW LVIII: verified loop surjectivity and the remaining citation gap

Date: 2026-09-05. **Primary-source audit; no open-problem resolution.**

The [coefficient-unitary note](../../notes/stw58-coefficient-unitary-stabilization-2026-09-05.md),
under “A citation boundary in degree one,” already distinguishes the
published degree-one assertion from its unverified derivation.
This supplement adds an explicit proof of loop surjectivity, the
latest CGSTW cross-check, and an alternative injectivity criterion.
Reinspection of the old citation is not new mathematical progress.

## 1. What the scanned original actually assumes

M. A. Rieffel, *The homotopy groups of the unitary groups of
non-commutative tori*, J. Operator Theory 17 (1987), 237–254:
[original PDF](https://jot.theta.ro/jot/archive/1987-017-002/1987-017-002-005.pdf).

Writing \(T^jA=C(\mathbb T^j,A)\), Theorem 3.3 on printed page
244 assumes that \(A\) is unital and that
\[
\operatorname{csr}(T^jA)\le p\quad\text{for every }j\ge0.
\tag{1}
\]
It concludes canonical stable identifications
\(\pi_k(GL_n(A))=K_{k+1}(A)\) for \(n\ge p-1\) and all \(k\ge0\),
with the usual two-periodic interpretation of \(K\)-groups.
The proof uses Proposition 3.2 and the last-column homotopy
exact sequence. It does not state (1) under stable rank one alone.

On printed page 243, Theorem 2.10 gives
\[
GL_n(A)/GL_n(A)^0\cong K_1(A)
\quad(n\ge\operatorname{tsr}(A)).
\tag{2}
\]
The preceding paragraph records
\[
\operatorname{csr}(A)\le\operatorname{tsr}(A)+1,\qquad
\operatorname{csr}(TA)\le\operatorname{tsr}(A)+1,
\tag{3}
\]
the second bound citing Corollary 8.6 of Rieffel's 1983 paper.
Thus stable rank one certainly gives the canonical degree-zero
bijection \(U(A)/U_0(A)\cong K_1(A)\), by polar deformation.

## 2. A complete derivation of degree-one surjectivity

**Prior-art consequence.** If \(A\) is unital of stable rank one,
the canonical map
\[
\pi_1(U(A),1)\longrightarrow K_0(A)
\tag{4}
\]
is surjective.

**Proof.** Equation (3) gives \(\operatorname{csr}(TA)\le2\).
For \(n\ge2\), the space \(Lg_n(TA)\) of left unimodular
\(n\)-tuples is therefore path connected. There is a natural
identification
\[
Lg_n(TA)=C(\mathbb T,Lg_n(A)).
\]
Indeed pointwise invertibility of the positive sum defining a
unimodular tuple gives uniform invertibility on the compact
circle. The identification respects the norm topologies.

Every circle map into \(Lg_n(A)\) is consequently freely
null-homotopic. This implies \(\pi_1(Lg_n(A))=0\): the change
from free to based homotopy only conjugates a loop class, and
a conjugate of the identity is the identity. Also \(Lg_n(A)\)
is path connected by \(\operatorname{csr}(A)\le2\).

Use the last-column fibration from Section 1 of Rieffel's
paper. The general linear group acts transitively on the tuple
space in this range, and its stabilizer is homotopy equivalent
to \(GL_{n-1}(A)\). The exact sequence contains
\[
\pi_1(GL_{n-1}(A))\longrightarrow
\pi_1(GL_n(A))\longrightarrow\pi_1(Lg_n(A))=0.
\]
Thus every adjacent stabilization is surjective on fundamental
groups. Every stable loop class has a finite matrix representative,
so repeated surjectivity, polar deformation, and Bott periodicity
prove (4). \(\square\)

This is the loop-surjectivity mechanism used with Rieffel's
Proposition 2.6. Gong–Lin–Xue, *Determinant rank of \(C^*\)-algebras*,
Pacific J. Math. 274 (2015), 403–436, printed page 416, independently
uses that proposition in Theorem 3.10 and the bound (3) in
Corollary 3.11.
[Publisher's paper](https://msp.org/pjm/2015/274-2/pjm-v274-n2-p06-p.pdf).

Injectivity does not follow from this argument: the preceding
term \(\pi_2(Lg_n(A))\) in the same exact sequence has not been
eliminated by the connected-stable-rank estimate for \(TA\).

## 3. The later assertions and an alternate criterion

Sarkowicz's published *Unitary groups, K-theory, and traces*,
Glasgow Math. J. 66 (2024), 229–251, printed page 230,
equation (1.2) and its following paragraph, explicitly asserts
that (4) is an isomorphism for stable rank one, citing Rieffel
1987 as [32]. It is repeated on printed page 235 before (3.6).
[Published article](https://doi.org/10.1017/S0017089523000447).
The [arXiv version history](https://arxiv.org/abs/2305.15989)
ends at v2, 21 November 2023; its GL-variant correction does
not remove the published degree-one assertion.

The new cross-check is Carrión–Gabe–Schafhauser–Tikuisis–White,
*Classifying \(*\)-homomorphisms I: Unital simple nuclear
\(C^*\)-algebras*, arXiv:2307.06480v4, 13 August 2026:
printed page 30, Remark 2.8, explicitly asserts both the
degree-zero and degree-one bijections for stable rank one,
citing [249, Theorem 3.3]. Reference [249] is Rieffel 1987.
[Version v4](https://arxiv.org/pdf/2307.06480v4).
This was Remark 2.7, printed page 31, citing [232, Theorem 3.3],
in the [earlier author-hosted version](https://faculty.tcu.edu/jcarrion/pdf/CGSTW23.pdf).
The remark's stable-rank-one assertion is not restricted to
the paper's \(\mathcal Z\)-stable codomains.

An exact alternative criterion is available in Vaidyanathan,
*Homotopical stable ranks for certain \(C^*\)-algebras*,
Theorem 3.7 of
[arXiv:1710.10009v4](https://arxiv.org/pdf/1710.10009v4):
\[
\operatorname{gsr}(C(\Sigma X)\otimes A)
 =\max\{\operatorname{gsr}(A),\operatorname{inj}_X(A)\}.
\tag{5}
\]
Here \(\operatorname{inj}_X(A)\) is the least \(n\ge1\)
for which every stabilization
\([X,GL_{m-1}(A)]_*\to[X,GL_m(A)]_*\), \(m\ge n\), is injective.
For stable rank one, \(\operatorname{gsr}(A)=1\). Taking
\(X=S^1\), (5) shows that
\[
\operatorname{gsr}(C(S^2)\otimes A)=1
\tag{6}
\]
is equivalent to injectivity of all adjacent matrix
stabilizations on unitary fundamental groups. In particular
(6) would prove injectivity in (4). This gives a precise
sufficient condition without assuming all-torus connectivity.
We have not deduced (6) from stable rank one.

## 4. Exact audit conclusion and provenance

The verified route proves degree-zero bijectivity and
degree-one surjectivity. Later research papers explicitly assert
the stronger degree-one bijectivity, but the cited Theorem 3.3
has the extra hypothesis (1). This audit has not supplied the
additional argument or another complete proof under stable rank
one alone. The bounded search found no counterexample and no
erratum addressing that assertion.

This is a derivation/citation gap in our verification. It does
not show the later assertions are false, establish a mathematical
open status for degree one, or justify declaring degree two the
first open degree. The finite simple pure slice supplies stable
rank one via Lin, so the verified statements apply there; the
specific injectivity derivation remains unverified.

Web screenshots of the scanned original were unusable in the
present tool wrappers. The root rendered pages through MSI,
and both agents visually inspected:

- [Printed page 243](/Users/user/stw-rieffel-page-7.png):
  (2), (3), and the start of Section 3.
- [Printed page 244](/Users/user/stw-rieffel-page-8.png):
  Propositions 3.1–3.2 and Theorem 3.3 with its proof.
- [Printed page 245](/Users/user/stw-rieffel-page-9.png):
  the torus specialization and separate divisibility hypotheses.

The original source URL and printed page numbers are the
durable citations; the local files record the scan inspection.
No old research files were changed for this audit.
