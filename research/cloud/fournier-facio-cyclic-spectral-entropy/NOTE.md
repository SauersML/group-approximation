# Cyclic spectral entropy on the Fournier--Facio fixed-block sector

## 1. Question and choice of branch

I use the positive (matrix-model) branch for the torsion-free
Fournier--Facio examples.  The input from the repository is the common-block
reduction and, in particular, the pointwise Haar-moment law proved in
`research/fournier-facio-fixed-block-haar-moment-proof.md`.  This note does
**not** prove that those groups are hyperlinear.  It strengthens the necessary
condition on the only common-block models which remain after the existing
no-go results.

The earlier result says that on a positive-charge fixed-block sector, for the
distinguished actor `U`, every fixed nonzero return coefficient

\[
        \langle U^k\delta_x,\delta_x\rangle
\]

vanishes in charge.  It was used there to exclude a bounded number of
distinct eigenvalues in aggregate.  The theorem below is columnwise and
quantitative: almost every charged column must see arbitrarily large
**effective spectral support**, even if the ambient block has many irrelevant
eigenvalues.

## 2. A finite-dimensional moment--entropy inequality

Let `U` be a unitary on a finite-dimensional Hilbert space and let `xi` be a
unit vector.  Write

\[
 m_k=\langle U^k\xi,\xi\rangle \quad(k\in\mathbb Z).
\]

Let `U=sum_j lambda_j E_j` be its spectral decomposition after combining
equal eigenvalues, and put `p_j=||E_j xi||^2`.  Discard the zero `p_j` and
define the order-two (collision) entropy

\[
 H_2(U,\xi)=-\log\sum_jp_j^2.
\]

### Theorem 2.1 (cyclic moment--rank--entropy bound)

For every integer `N>=0`,

\[
 \min\left\{\exp H_2(U,\xi),
 \operatorname {rank}\{\xi,U\xi,\ldots,U^N\xi\}\right\}\ \geq
 \frac{(N+1)^2}
 {(N+1)+2\sum_{k=1}^N(N+1-k)|m_k|^2}.                 \tag{2.1}
\]

Consequently, if `|m_k|<=epsilon` for `1<=k<=N`, then

\[
 \operatorname {rank}\{\xi,U\xi,\ldots,U^N\xi\}
 \geq \frac{N+1}{1+N\epsilon^2}.                     \tag{2.2}
\]

The two quantities on the left need not be ordered; the assertion is that
the same moment expression bounds both of them.

### Proof

Let `G=(m_(j-i))_(0<=i,j<=N)` be the Gram matrix of the displayed Krylov
vectors.  It is positive semidefinite,

\[
 \operatorname {tr}G=N+1,
 \qquad
 \operatorname {tr}(G^2)
 =(N+1)+2\sum_{k=1}^N(N+1-k)|m_k|^2.                 \tag{2.3}
\]

If `r=rank(G)`, Cauchy--Schwarz applied to its nonzero eigenvalues gives
`(tr G)^2 <= r tr(G^2)`.  This proves the second inequality in (2.1).

For the entropy inequality, the nonnegative Fejer kernel

\[
 F_N(z)=\frac1{N+1}\left|1+z+\cdots+z^N\right|^2
       =\sum_{k=-N}^N\left(1-\frac{|k|}{N+1}\right)z^k
\]

gives

\[
 \frac{(N+1)+2\sum_{k=1}^N(N+1-k)|m_k|^2}{(N+1)^2}
 =\frac1{N+1}\sum_{i,j}p_ip_jF_N(\lambda_i\overline{\lambda_j})
 \geq\sum_jp_j^2.                                    \tag{2.4}
\]

Indeed, expand the middle expression and use
`|m_k|^2=sum_(i,j)p_i p_j(lambda_i conjugate(lambda_j))^k`; all off-diagonal
terms in the last expression are nonnegative, and `F_N(1)=N+1`.  Inverting
(2.4) proves the entropy half of (2.1).  Finally
`2 sum_(k=1)^N (N+1-k)=N(N+1)`, which turns (2.1) into (2.2).  ∎

## 3. Application to the charged fixed-block actor

Use the notation of the repository's Haar-moment theorem:

\[
 F=\bigcup_{y\in F_g}X_y,\qquad U=P_FB_gP_F,
\]

and let `mu` be its finitely additive basis charge.  For `x in F`, let
`H_2(x)` denote the collision entropy of the spectral measure of `U` at
`delta_x` inside its finite block.

### Corollary 3.1 (columnwise entropy escapes every cutoff)

Assume the pointwise charged Haar law `(FFHM3)`.  For every integer `N>=1`
and every `0<epsilon<1`, outside a charged-null subset of `F`,

\[
 \begin{aligned}
 \operatorname {rank}\{\delta_x,U\delta_x,\ldots,U^N\delta_x\}
     &\geq \frac{N+1}{1+N\epsilon^2},\\
 H_2(x)&\geq
 \log\frac{N+1}{1+N\epsilon^2}.                      \tag{3.1}
 \end{aligned}
\]

In particular, for every finite `R`, the set of columns whose cyclic
spectral measure has collision-effective support at most `R` has charge
zero.

### Proof

For each `1<=k<=N`, `(FFHM3)` says that
`{x:|<U^k delta_x,delta_x>|>=epsilon}` has charge zero.  A finite union is
null, so (2.2) applies off that union and gives (3.1).

Given `R`, choose `N` with `N+1>2R` and then choose
`epsilon<=N^(-1/2)`.  The right side of the entropy-free version of (3.1)
is at least `(N+1)/2>R`.  Therefore every column of effective support at
most `R` belongs to the finite null union.  ∎

This is strictly more local than counting distinct eigenvalues of the whole
block.  A block may have arbitrarily many eigenvalues while a chosen basis
column is concentrated on two of them; Corollary 3.1 rules out positive
charge carried by such columns.  It also rules out unbounded spectra with
uniformly bounded inverse participation ratio.

## 4. Concrete tests and sharpness

The script `verify.py` checks (2.1) directly from spectral weights and also
from Krylov Gram matrices.

* **Calibration:** the cyclic shift on `L` points, at a coordinate vector,
  has `m_k=0` for `1<=k<L`.  Its first `N+1<=L` Krylov vectors are exactly
  orthonormal, so the rank bound is equality.
* **Independent test:** a five-phase diagonal unitary conjugated by a fixed
  non-Fourier orthogonal matrix has nonuniform spectral weights.  The script
  verifies the trace formula, the rank bound, and the entropy bound.  This is
  not a shift model and is not specialized from the calibration case.

These finite computations are tests of the algebra in (2.1), not evidence
for existence of the required near representation.

## 5. Literature and repository audit

The moment-matrix argument is the standard elementary Gram/rank inequality;
no priority claim is made for Theorem 2.1 in isolation.  The new content of
this note is its application to the repository's finitely additive,
pointwise charged Haar law, yielding the columnwise conclusion in Corollary
3.1.  Repository searches for `Krylov window`, `spectral entropy`,
`charge-haar`, and `collision entropy` found the aggregate Haar law and the
global distinct-eigenvalue escape, but not this inverse-participation
conclusion.

The group-theoretic input remains Fournier--Facio's torsion-free explicit
nonsofic construction and the Kahl--Schneider near-action formulation as
recorded and cited in the repository's Fournier--Facio claim files.  A web
literature query was attempted on 2026-09-08, but the configured search
endpoint returned HTTP 401; therefore this note makes no claim that the
external priority search is exhaustive.

## 6. Exact open residue

Name the remaining assertion:

> **OPEN (joint high-entropy compression coupling).** Construct, or rule out,
> a purely singular invariant amenable near representation of a
> Fournier--Facio torsion-free nonsofic group whose positive fixed-block
> actor has columnwise collision entropy escaping every cutoff and whose
> other actors satisfy both compression relations on the same charged
> columns.

One-actor entropy cannot close the problem: long cyclic blocks attain the
conclusion exactly.  Any next obstruction must use a joint invariant (for
example mutual spectral information between a fixed actor and a compressor),
not another marginal recurrence statistic.

## Status

* **PROVED:** The finite-dimensional moment--rank--collision-entropy
  inequality (2.1), including the explicit bound (2.2).
* **PROVED, conditional only on an already established repository input:**
  Corollary 3.1 follows from the pointwise charged Haar law `(FFHM3)` and
  says that cyclic effective spectral support escapes every finite cutoff
  columnwise in charge.
* **CONDITIONAL:** Applicability to a proposed common-block hyperlinear model
  assumes that it has first been reduced to the fixed sector and charged
  Haar law exactly as in the cited repository claims.
* **OPEN:** Existence of that model, the joint high-entropy compression
  coupling above, hyperlinearity of the Fournier--Facio groups, existence of
  a hyperlinear nonsofic group, and existence of a nonhyperlinear group.
