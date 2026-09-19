# LXI: alternating conjugates cannot give a strict commutator squeeze

Date: 2026-09-05. **Complete proof of the stated obstruction.**
This concerns a specified class of mixed projections. It does not settle LXI.

## 1. Statement

Let \(A\) and \(v\in U(A)\) be the simple AH algebra and unitary
from the LIX construction. Choose the initial generator
\(S^4\to SU(2)\) representing the nonzero element of
\(\pi_4(SU(2))\). Its image is all of \(SU(2)\): omitting a point
would make the map null-homotopic. Consequently
\(\sigma(v)=S^1\). Put
\[
B=A*_{\mathbb C}T_2
\]
and regard \(v\) and the canonical Toeplitz isometries
\(s_1,s_2\) as elements of \(B\).

**Theorem.** Let \(p\) be any nontrivial projection of \(T_2\).
For every finite alternating product
\[
w=a_0v^{k_1}a_1v^{k_2}a_2\cdots v^{k_m}a_m,
\qquad a_j\in U(T_2),\quad k_j\in\mathbb Z,
\tag{1.1}
\]
the projection \(q=wpw^*\) satisfies
\[
\boxed{\ \|[v,q]\|=1.\ }
\tag{1.2}
\]
The coefficients \(a_j\) may be arbitrary Toeplitz unitaries;
they need not be polynomial in the generators.

In particular, take \(p=s_1s_1^*\). Then \(q\) and \(1-q\) are
properly infinite and full, but no alternating product (1.1)
can make the commutator norm strictly less than \(1\).
This excludes the BRR Lemma 2.4(ii) squeeze for all these
conjugates, including ones escaping every fixed Toeplitz corner.

This result is distinct from the fixed-corner rotation
obstruction: (1.1) may move the support through many
\(v\)-translates of the Toeplitz algebra.

## 2. The universal subalgebra

Because \(\sigma(v)=S^1\), the map \(z\mapsto v\) identifies
\(C^*(v)\) with \(C(S^1)\). The inclusion theorem for full
amalgamated free products, with amalgamating algebra
\(\mathbb C\) unchanged, gives an injective homomorphism
\[
C(S^1)*_{\mathbb C}T_2
\longrightarrow A*_{\mathbb C}T_2.
\tag{2.1}
\]
Thus \(C=C^*(v,T_2)\subset B\) is isometrically the full free
product on the left. We may compute a lower norm bound using
any representation of \(C\).

The precise source for (2.1) is Armstrong–Dykema–Exel–Li,
*On embeddings of full amalgamated free product C*-algebras*,
Proposition 2.2. Its hypotheses require the same
amalgamating algebra, as is the case here.
[Primary paper](https://arxiv.org/pdf/math/0210448).

## 3. A shift representation

Form the infinite minimal tensor product
\[
D=\bigotimes_{n\in\mathbb Z}T_2
\]
with respect to the units. Concretely, this is the unital
inductive limit of finite tensor products over finite
intervals in \(\mathbb Z\), with connecting maps inserting
identity elements. These maps are injective and isometric:
in the minimal tensor product,
\(\|x\otimes1\|=\|x\|\), as is seen in faithful spatial
representations. Hence every finite tensor product, and
every individual site map
\[
\iota_n:T_2\to D,
\]
is faithful.

There is a shift automorphism \(\alpha\) of \(D\) satisfying
\(\alpha(\iota_n(a))=\iota_{n+1}(a)\). Let
\[
E=D\rtimes_\alpha\mathbb Z
\]
be the full crossed product and let \(U\) be its implementing
unitary, with convention
\[
U d U^*=\alpha(d).
\tag{3.1}
\]
The coefficient inclusion \(D\to E\) is faithful. For an
explicit verification, choose a faithful representation
\(\rho:D\to B(\mathcal H)\). On
\(\ell^2(\mathbb Z,\mathcal H)\), define
\[
(\Pi(d)\xi)(n)=\rho(\alpha^{-n}(d))\xi(n),
\qquad
(S\xi)(n)=\xi(n-1).
\]
Then \(S\Pi(d)S^*=\Pi(\alpha(d))\), and \(\Pi\) is faithful
because its coordinate-zero restriction is \(\rho\).
The universal crossed product therefore has a representation
faithful on its coefficient algebra.

The universal property of the full free product gives a
unital homomorphism
\[
\Phi:C(S^1)*_{\mathbb C}T_2\to E,
\qquad
\Phi(v)=U,\quad \Phi(a)=\iota_0(a)\ (a\in T_2).
\tag{3.2}
\]
It is in fact onto, since \(U\) and \(\iota_0(T_2)\) generate
all the shifted sites. Surjectivity is not needed for the
norm estimate.

Crucially, (3.2) is a map on the universal subalgebra \(C\),
not an asserted homomorphism on all of \(B\). Injectivity
of (2.1) is what permits its use for norms in \(B\).

## 4. The alternating-word calculation

Put
\[
n_0=0,\qquad n_j=k_1+\cdots+k_j,\qquad K=n_m.
\]
The word (1.1) has the exact form
\[
w=bv^K,\qquad
b=\prod_{j=0}^{m}v^{n_j}a_jv^{-n_j},
\tag{4.1}
\]
where products retain their original order. It follows that
\[
\Phi(q)=
\left(\prod_{j=0}^{m}\iota_{n_j}(a_j)\right)
\iota_K(p)
\left(\prod_{j=0}^{m}\iota_{n_j}(a_j)\right)^*.
\tag{4.2}
\]
Distinct tensor sites commute. All letters in (4.2) at
sites other than \(K\) therefore cancel through
\(\iota_K(p)\). If
\[
c=\prod_{\substack{0\le j\le m\\n_j=K}}a_j
\]
in the original subsequence order, and \(P=cpc^*\), then
\[
\Phi(q)=\iota_K(P),\qquad
\Phi(vqv^*)=\iota_{K+1}(P).
\tag{4.3}
\]
The element \(P\) is a nontrivial projection of \(T_2\).

In the faithful two-site tensor product,
\[
\|\iota_{K+1}(P)-\iota_K(P)\|=1.
\tag{4.4}
\]
Indeed, take a faithful Hilbert-space representation of
\(T_2\). Both the range and kernel of \(P\) are nonzero.
A tensor product of a vector in one range and a vector
in the other kernel is an eigenvector with eigenvalue
\(1\) or \(-1\) for \(P\otimes1-1\otimes P\).
The upper bound is \(1\) because the two projections
commute. Faithfulness of the tensor-site and crossed-product
inclusions preserves this norm.

Finally, (2.1)–(4.4) give
\[
\|[v,q]\|_B
=\|vqv^*-q\|_C
\ge\|\Phi(vqv^*-q)\|_E
=1.
\]
For every unitary \(v\) and projection \(q\),
\(\|[v,q]\|\le1\). In the decomposition given by \(q\),
the commutator has off-diagonal blocks
\(-qv(1-q)\) and \((1-q)vq\), both contractions.
This proves (1.2).

For \(p=s_1s_1^*\), the projection \(p\) is equivalent
to the properly infinite unit, while \(1-p\) contains
\(s_2s_2^*\), also equivalent to the unit. Thus both
are properly infinite and full. Conjugation by \(w\)
preserves these properties, establishing the final
assertion of the theorem. \(\square\)

## 5. Exact scope

The theorem permits arbitrary length, arbitrary integer
powers of \(v\), arbitrary Toeplitz unitaries, repeated
visits to tensor sites, and arbitrary cancellation in
the word. It includes the norm closure of the resulting
set of conjugate projections, since the commutator norm
is continuous.

It does not treat arbitrary unitaries in \(C^*(v,T_2)\).
In particular, a unitary obtained by taking linear
combinations of alternating words and then applying
functional calculus need not have form (1.1).
The shift image of its conjugate projection need not
be supported at a single tensor site. General unitary
functions \(f(v)\) in an alternating expression are
also outside the stated class unless they are scalar
multiples of integer powers of \(v\).
Finally, words involving other generators of \(A\)
are not covered by the universal-subalgebra argument.

The result supplies an exact obstruction for all
alternating conjugates (1.1), not a non-null-homotopy
proof for \(v\) in \(B\), and not a solution of LXI.
