# LXI: exact norm obstruction for mixed rotations inside a Toeplitz corner

Date: 2026-09-05. **Proved obstruction for the specified class; LXI remains open.**
This note does not assert survival of the free-envelope unitary.

## 1. Setup and the universal subalgebra

Let \(A\) be the simple AH algebra from the LIX construction, with witness
\(v\). Choose its initial generator \(S^4\to SU(2)\) nontrivial in
\(\pi_4(SU(2))\). Its image is all of \(SU(2)\), since a map omitting
one point factors through a contractible space. Hence
\(\sigma(v)=S^1\). Put
\[
B=A*_{\mathbb C}T_2,\qquad
C=C^*(v,T_2)\subset B.
\]
The natural homomorphism
\[
C(S^1)*_{\mathbb C}T_2\longrightarrow B
\]
is injective, so \(C\) is the indicated full free product. Here we use
the full-free-product inclusion theorem with the common amalgamating
algebra unchanged, not a reduced-free-product argument:
Armstrong–Dykema–Exel–Li, *On embeddings of full amalgamated free product
C*-algebras*, Proposition 2.2.
[Primary paper](https://arxiv.org/pdf/math/0210448).

Let \(s_1,s_2\) be the canonical Toeplitz isometries. Their ranges are
orthogonal, and
\[
P=s_1s_1^*+s_2s_2^*<1.
\]
The strict inequality holds in \(T_2\), for example in its faithful
Fock representation.

## 2. Arbitrary mixed coefficients inside a fixed factor corner

**Theorem.** Let \(0<P<1\) be a projection of the Toeplitz factor.
If \(q\in C\) is a full projection and \(q\le P\), then
\[
\|[v,q]\|=1.
\tag{2.1}
\]
More generally, the same equality holds for
\(v^kqv^{-k}\), for every integer \(k\).

**Proof.** Choose an infinite amplification
\(\rho:T_2\to B(\mathcal H)\) of a faithful representation.
Both \(\rho(P)\mathcal H\) and
\((1-\rho(P))\mathcal H\) are infinite-dimensional separable
Hilbert spaces. There is therefore a self-adjoint unitary \(V\)
interchanging them:
\[
V\rho(P)V^*=1-\rho(P).
\]
The universal property gives a unital representation
\[
\pi:C(S^1)*T_2\to B(\mathcal H)
\]
whose restrictions are \(v\mapsto V\) and \(\rho\).
Since \(q\) is full and \(\pi\) is unital, \(\pi(q)\ne0\).
The inclusion \(q\le P\) gives
\[
\pi(q)\le\rho(P),\qquad
V\pi(q)V^*\le1-\rho(P).
\]
These two nonzero projections are orthogonal. Hence
\[
\|[V,\pi(q)]\|
=\|V\pi(q)V^*-\pi(q)\|=1.
\]
The norm in \(C\) is at least this representation norm, and its
norm in \(B\) is the same by the inclusion theorem above.
For every unitary and projection the commutator norm is at most
\(1\), as follows by writing the commutator in the two-by-two
decomposition given by the projection. This proves (2.1).
Conjugating \(q\) by \(v^k\) leaves the commutator norm unchanged.
\(\square\)

This theorem permits \(q\) to depend on both \(v\) and all Toeplitz
generators in an arbitrary way. Its restriction is the support
condition \(q\le P\), not the absence of mixed coefficients.

## 3. The explicit rotation family

For \(0\le\theta\le\pi/2\), define
\[
r_\theta=s_1\cos\theta+s_2v\sin\theta,\qquad
q_\theta=r_\theta r_\theta^*.
\tag{3.1}
\]
Orthogonality of \(s_1,s_2\) gives \(r_\theta^*r_\theta=1\).
Thus \(q_\theta\) is full and properly infinite, being equivalent
to the properly infinite unit of \(C\). It is supported in the
fixed proper projection \(P\).

This is explicitly a conjugate of \(s_1s_1^*\). The matrix
\[
R_\theta=
\begin{pmatrix}
\cos\theta&-v^*\sin\theta\\
v\sin\theta&\cos\theta
\end{pmatrix}\in U(M_2(C))
\]
is unitary. Under the corner homomorphism
\[
\Theta([a_{ij}])=\sum_{i,j=1}^{2}s_i a_{ij}s_j^*
\]
put
\[
W_\theta=\Theta(R_\theta)+(1-P).
\]
Then \(W_\theta\) is a unitary, \(W_0=1\), and
\[
q_\theta=W_\theta(s_1s_1^*)W_\theta^*.
\]
Its complement contains the range of the second column isometry
\[
t_\theta=-s_1v^*\sin\theta+s_2\cos\theta.
\]
Consequently both \(q_\theta\) and \(1-q_\theta\) are properly
infinite and full.

Nevertheless, for every angle,
\[
\boxed{\ \|[v,q_\theta]\|=1.\ }
\tag{3.2}
\]
Thus no angle in this genuinely mixed rotation gives the strict
inequality needed by BRR Lemma 2.4(ii).

## 4. Arbitrarily large matrix rotations and finite compositions

Let \(t_1,\ldots,t_n\) be Toeplitz-factor isometries with pairwise
orthogonal ranges and with
\[
P_n=\sum_{j=1}^nt_jt_j^*<1.
\]
For any \(R\in U(M_n(C))\), including one whose entries contain
arbitrarily long alternating words in \(v\) and the Toeplitz
generators, set
\[
W_R=\sum_{i,j}t_iR_{ij}t_j^*+(1-P_n),\qquad
q_R=W_Rt_1t_1^*W_R^*.
\]
The projection \(q_R\) is full, equivalent to \(1\), and satisfies
\(q_R\le P_n\). The theorem therefore gives
\[
\|[v,q_R]\|=1.
\tag{4.1}
\]
For \(n\ge2\), its complement contains another column range and
is properly infinite and full as well.

Any finite product of such rotations using the same supporting
Toeplitz corner still has this form, with matrix coefficient
equal to the product of the coefficient matrices. More generally,
all unitaries commuting with a fixed proper Toeplitz projection
and carrying a full subprojection into that corner are covered
by Theorem 2.1.

## 5. What is not decided

The theorem does not cover an arbitrary alternating unitary
\[
w=a_0v^{k_1}a_1\cdots v^{k_m}a_m,
\qquad a_j\in U(T_2),
\]
when \(w s_1s_1^*w^*\) is not supported in any fixed proper
Toeplitz projection or one of its \(v\)-translates. Nor does it
cover arbitrary projections using additional generators of
\(A\) outside \(C^*(v)\).

The explicit mixed rotation family, all higher matrix versions,
and all finite compositions within a fixed Toeplitz corner
have been ruled out by an exact norm computation. No universal
obstruction for unrestricted mixed words is asserted.
