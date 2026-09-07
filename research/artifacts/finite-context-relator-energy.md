# Finite-context relator energy detects the ordinary word kernel

Research date: 2026-09-07.

## Result and boundary

This note proves an exact characterization of the words admitting a universal
finite-context quadratic relator certificate. They are precisely the words
equal to the identity in the presented group. In particular, such a certificate
cannot detect a **nontrivial** element of the MF radical, even after adding
arbitrarily many fixed polynomial right contexts.

This strengthens the repository's
[single-vector finite-ball observation](../../notes/PROPERTY_T_FREE_FINITE_BALL_LIMIT_2026-09-07.md).
It does not prove a new non-MF or non-hyperlinear existence theorem, and it
does not settle the property-(T)-free manuscript goal. These are ordinary
mathematical proofs; no Lean verification or literature priority is claimed.

## Conventions

Let $F=F(s_1,\ldots,s_m)$, with $m\geq1$, and let

$$G=F/\langle\!\langle R\rangle\!\rangle.$$

The relator set $R$ need not be finite. Words are elements of $F$, and
$|q|$ denotes reduced length. An $m$-tuple $U$ of unitaries on one Hilbert
space defines an evaluation of $\mathbb C[F]$; a word
$a_1\cdots a_k$ acts on a vector with $a_k$ acting first. Put

$$D_r(U)=r(U)-I,\qquad |X|^2=X^*X.$$

A polynomial context means an element $b\in\mathbb C[F]$ of finite support.
All constants, relators, and contexts in a certificate are fixed before the
matrix dimension and $U$ are chosen. Matrix inequalities below are in the
positive-semidefinite order, not inequalities of scalar operator norms.

## 1. A simultaneous finite-context countermodel

**Theorem 1.** Suppose $w_G\ne1$. Given finitely many pairs
$(r_j,b_j)$ with $r_j\in R$ and $b_j\in\mathbb C[F]$, there are
finite permutation matrices $U_1,\ldots,U_m$ and a unit vector $\xi$ such that

$$D_{r_j}(U)b_j(U)\xi=0\quad\text{for every }j,
\qquad \|(w(U)-I)\xi\|^2=2. \tag{1}$$

If $T$ is the union of the supports of the $b_j$, it suffices to use a
group word ball of radius

$$L=\max\left(1,|w|,
  \max_{j,\,q\in\operatorname{supp}b_j}(|r_j|+|q|)\right), \tag{2}$$

where the maximum over an empty set is omitted. In particular the dimension
is at most $1+\sum_{k=1}^L2m(2m-1)^{k-1}$.

**Proof.** Let $B_L\subseteq G$ be the word ball. For each generator,
left multiplication by $s_i$ is a bijection between the two finite sets

$$\{g\in B_L:s_i g\in B_L\},\qquad
  \{s_i g:g\in B_L, s_i g\in B_L\}.$$

Extend this partial bijection to a permutation $\sigma_i$ of $B_L$ by
matching the remaining domain and range points. Define
$U_i\delta_g=\delta_{\sigma_i(g)}$ and $\xi=\delta_1$.
The inverse permutation agrees with multiplication by $s_i^{-1}$ whenever
both endpoints are in $B_L$: the corresponding forward edge was prescribed.

For every word of written length at most $L$, every suffix path from $1$
stays in $B_L$. Induction on the letters applied, from right to left, gives

$$q(U)\xi=\delta_{q_G}. \tag{3}$$

Choose reduced representatives of $r_j$ and $q$. Both the word $q$ and the
concatenation $r_jq$ have written length at most $L$. Since $r_j=1$ in $G$,

$$D_{r_j}(U)q(U)\xi
 =\delta_{(r_jq)_G}-\delta_{q_G}=0.$$

Taking the finite linear combination defining $b_j$ proves its equation in
(1). Equation (3) for $w$ gives two distinct orthonormal basis vectors, so
the remaining squared norm is $2$. The dimension bound counts reduced free
words mapping onto $B_L$. $\square$

This is an existence construction. For a presentation with an undecidable
word problem, the proof does not give an algorithm to compute $B_L$ from
the relator list.

**Corollary 2.** If $w_G\ne1$, no choice of finitely many $(r_j,b_j)$,
$C\geq0$, and $0\leq\varepsilon<2$ makes

$$|w(U)-I|^2\ \leq\
 C\sum_j b_j(U)^*|D_{r_j}(U)|^2b_j(U)+\varepsilon I \tag{4}$$

hold for every finite-dimensional unitary tuple $U$.

**Proof.** The quadratic form on the vector (1) would say
$2\leq\varepsilon$. $\square$

The same countermodel kills any finite sum of vectors
$a(U)D_r(U)b(U)\xi$: left polynomial multipliers cannot repair a zero right
factor. It therefore also excludes a finite family of squares of such sums
on the right of (4).

## 2. The converse, with an explicit sum of squares

**Theorem 3.** The following are equivalent for $w\in F$:

1. $w_G=1$.
2. There are finitely many $r_j\in R$, polynomial contexts $b_j$, and
   $C\geq0$ for which (4) holds with $\varepsilon=0$ in every matrix dimension.
3. There are such data for which (4) holds with some
   $0\leq\varepsilon<2$ in every matrix dimension.

Moreover, from an explicit normal-closure expression

$$w=\prod_{j=1}^N a_j,
\qquad a_j=g_jr_j^{\epsilon_j}g_j^{-1},
\qquad \epsilon_j\in\{1,-1\}, \tag{5}$$

one obtains a certificate with word contexts $b_j=g_j^{-1}$ and $C=N$.
Its positivity has an explicit identity in the integral free group ring.

**Proof.** Implication 2 to 3 is immediate. Implication 3 to 1 is
Corollary 2. For 1 to 2, membership in the normal closure means precisely
that a finite expression (5) exists. Write $p_0=1$,
$p_j=a_1\cdots a_j$, and

$$z_j=p_{j-1}(a_j-1).$$

Telescoping gives $\sum_jz_j=w-1$. If $\epsilon_j=1$, then

$$z_j=p_{j-1}g_j(r_j-1)g_j^{-1}.$$

If $\epsilon_j=-1$, use $r_j^{-1}-1=-r_j^{-1}(r_j-1)$ to obtain

$$z_j=-p_{j-1}g_jr_j^{-1}(r_j-1)g_j^{-1}.$$

Thus in both cases the left multiplier of $(r_j-1)g_j^{-1}$ is a
signed group element and has $L^*L=1$. Consequently

$$z_j^*z_j=(g_j^{-1})^*(r_j-1)^*(r_j-1)g_j^{-1}. \tag{6}$$

For arbitrary elements $z_1,\ldots,z_N$ of a complex star algebra, direct
expansion yields the ordered, noncommutative identity

$$N\sum_j z_j^*z_j-
 \left(\sum_jz_j\right)^*\left(\sum_jz_j\right)
 =\sum_{i<j}(z_i-z_j)^*(z_i-z_j). \tag{7}$$

Indeed each diagonal term occurs $N-1$ times on the right and each ordered
off-diagonal product occurs with coefficient $-1$. Substituting (6) and
$\sum_jz_j=w-1$ proves the advertised identity, with integer coefficients.
Evaluation at unitaries makes the right side positive. If $N=0$, then
$w=1$ already in $F$ and the zero certificate suffices. $\square$

For example, a displayed product of $N$ conjugate relators gives a
certificate with $N(N-1)/2$ explicitly named square terms. This is an upper
bound for this construction, not a minimal-certificate or Dehn-area
characterization.

## 3. What this decides for the MF search

Theorem 3 identifies the exact limitation of a proposed certificate class.
It does not merely show that a particular numerical search failed:
**no finite level in this entire class can certify a nontrivial word as an
MF-radical element.** This remains so if each new level adds longer fixed
contexts, different polynomial contexts, or a slack less than $2$.

This does not exclude a scalar global estimate such as

$$\|w(U)-I\|\leq C\max_{r\in R_0}\|r(U)-I\|,$$

or an implication conditional on all relators having small operator norm.
The construction controls relators only on the finitely named vectors;
their action elsewhere is unrestricted. It also says nothing against a
trace-based certificate with additional hypotheses, a dimension-dependent
adaptive collection of tests, or a non-polynomial construction with its own
justified global control. None of those is the universally quantified
positive-operator inequality (4).

The open mathematical work remains to find the required **global** control
for a specific nontrivial element. Replacing that work by (4), even with
translated tests, would change the target to the ordinary word problem.

## Prior art and checks

Repository lexical searches included `finite ball`, `right multipliers`,
`word energy domination`, and `sum of squares`, including the notes corpus.
The starting point is the linked repository note, whose permutation
construction is reused explicitly here.

Normal-closure expressions are standard presentation theory, and their
length is the usual relator-area notion; see the preliminaries of
[Wang, *Subgroup Distortion and the Relative Dehn Functions of Metabelian
Groups*](https://arxiv.org/html/2104.11828v1). Identity (7) is the standard
sum-of-pairwise-squared-differences identity. This note makes no claim that
these ingredients, or their combination, are new to the literature.

The research-status check also found
[Eckhardt, *Non-MF groups and non-finite full group C*-algebras*
(2026)](https://arxiv.org/html/2608.28772v1), which already states a non-MF
existence theorem and uses property (T). Accordingly, this work does not
present non-MF existence as an unsolved problem or relabel that paper's
argument as a new property-(T)-free proof.

Wolfram's context endpoint returned HTTP 404 during this session. No
Wolfram evaluation or certification is claimed.

## Continuation and exact replay

[Local context limits and global norm limits](local-context-and-global-norm-hierarchies.md)
proves that increasing the context depth all the way to infinity recovers
the full group C-star norm. It separately proves that the global
operator-norm hierarchy has the MF radical as its word kernel. Thus even
the limit of the vector hierarchy is the wrong invariant for the proposed
nontrivial-radical certificate.

The exact replay constructs a complete 1,199-point Heisenberg word ball and
checks 2,954 prescribed partial-permutation edges, 33 word-context pairs,
and nine polynomial-context pairs. All tested defect vectors vanish and
the target displacement squared is two. The three relators move 502, 250,
and 263 points elsewhere in the model, respectively. These nonzero defects
are why the witness does not claim an operator-norm approximation.

Five supplied normal-closure expressions, including inverse relators and
the empty expression, replay as exact free-group-ring identities. The
complete witness and certificate output are committed as
[`finite-context-heisenberg-witness.json`](finite-context-heisenberg-witness.json)
and [`finite-context-energy-replay.json`](finite-context-energy-replay.json).

From the repository root:

```sh
python -m unittest discover -s experiments -p test_finite_context_energy_audit.py -v
python experiments/finite_context_energy_audit.py \
  --verify-witness research/artifacts/finite-context-heisenberg-witness.json
```

The tests include rejection of a false word product, an incorrect inverse
sign, a nonbijective map, a changed internal edge, and an insufficient ball
radius. These finite checks supplement the proofs; they do not establish a
general theorem by sampling.
