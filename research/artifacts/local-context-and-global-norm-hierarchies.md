# Local context limits and global norm limits answer different questions

Research date: 2026-09-07.

This note continues [finite-context relator energy](finite-context-relator-energy.md).
It addresses the next attempted escape: perhaps testing **all** word contexts,
one finite depth at a time, eventually detects MF-invisible words. The answer
is no for the vector hierarchy defined below. Its limit is exactly the full
group C*-norm. In contrast, the global operator-norm hierarchy has precisely
the MF radical as its word kernel.

These are proved characterizations of two specific hierarchies. No new
non-MF or non-hyperlinear group, resolution of a major open problem, literature
priority, effective rate of convergence, or Lean certification is claimed.

## 1. Exact finite simulation of a prescribed orbit

**Lemma 1.** Let $T_1,\ldots,T_m$ be unitaries on an arbitrary Hilbert space
$\mathcal H$, let $\xi$ be a unit vector, and fix $L\geq1$. There is a
finite-dimensional subspace $K\subseteq\mathcal H$, containing $\xi$, and
unitaries $V_1,\ldots,V_m$ on $K$ such that

$$q(V)\xi=q(T)\xi\qquad (|q|\leq L). \tag{1}$$

One can take

$$K=K_L:=\operatorname{span}\{q(T)\xi:|q|\leq L\},
\qquad \dim K\leq D_L:=1+\sum_{k=1}^L2m(2m-1)^{k-1}. \tag{2}$$

**Proof.** Put $K_0=\mathbb C\xi$ and define $K_j$ as in (2). For each $i$,
the finite-dimensional subspaces

$$A_i=K_{L-1}+T_i^{-1}K_{L-1},\qquad
  B_i=T_iK_{L-1}+K_{L-1}$$

are contained in $K_L$. The restriction of $T_i$ is an isometric bijection
from $A_i$ onto $B_i$, so $\dim A_i=\dim B_i$. Their orthogonal complements
**inside $K_L$** have equal dimension. Complete this restriction by any
unitary between those complements, obtaining $V_i\in U(K_L)$.

For $\eta\in K_{L-1}$ we have $V_i\eta=T_i\eta$. Also
$T_i^{-1}\eta\in A_i$ and
$V_i(T_i^{-1}\eta)=\eta$, so $V_i^{-1}\eta=T_i^{-1}\eta$.
Thus the positive and negative letters both agree on $K_{L-1}$.
Inducting along the suffixes of any word of length at most $L$ proves (1).
The spanning set gives the dimension bound. $\square$

The inclusion of $T_i^{-1}K_{L-1}$ is essential: extending only the
restriction to $K_{L-1}$ would not justify agreement for inverse letters.
This lemma preserves a finite orbit, not the global relator norms of $T$.

## 2. The vector hierarchy converges to the full norm

Fix a finite presentation $G=\langle s_1,\ldots,s_m\mid R\rangle$,
$m\geq1$, and $f\in\mathbb C[F_m]$. Write $f_G$ for its image in
$\mathbb C[G]$ and $\|f_G\|_{\max}$ for its full group C*-norm. The
maximum relator length $\ell_R$ is zero when $R$ is empty; $\deg f$ is
the maximum reduced length in its support, with degree zero for the zero
polynomial.

For $n\geq0$ define

$$\beta_n(f)=\sup\left\{
 \|f(U)\xi\|^2:
 \begin{array}{l}
 d\geq1,\ U\in U(d)^m,\ \|\xi\|=1,\\
 (r(U)-I)q(U)\xi=0\quad(r\in R,\ |q|\leq n)
 \end{array}\right\}. \tag{3}$$

These are vector constraints. They do not say $r(U)=I$ as matrices.

**Theorem 2.** The feasible sets are nonempty and

$$\beta_n(f)\downarrow\|f_G\|_{\max}^2. \tag{4}$$

At each fixed $n$, the supremum in (3) is a maximum, and it suffices to use
the single dimension $D_L$ of (2), where
$L=\max(1,\deg f,n+\ell_R)$.

**Proof: the finite-dimension bound and attainment.** Start with any tuple
and vector occurring in (3), in any dimension. Lemma 1 preserves the vectors
for every word $q$ and $rq$ in the constraints, and for every word in $f$.
It therefore preserves both feasibility and the objective, in dimension at
most $D_L$. Pad smaller dimensions with identity matrices and pad the vector
with zeros. This gives exactly dimension $D_L$.

The corresponding feasible set is a closed subset of
$U(D_L)^m$ times its unit sphere. There are only finitely many constraints,
so this is compact and the objective attains its maximum. The all-identity
tuple makes the set nonempty. All objectives are bounded by
$\|f\|_{\ell^1(F_m)}^2$.

**Proof: lower bound.** Take any unitary representation $\pi$ of $G$ and
any unit vector $\eta$. The tuple $T_i=\pi(s_i)$ satisfies every relator
globally. Lemma 1, with the same $L$, produces a feasible finite-dimensional
tuple preserving $f(T)\eta$. Taking suprema over $\pi$ and $\eta$ gives

$$\beta_n(f)\geq\|f_G\|_{\max}^2. \tag{5}$$

**Proof: upper bound in the limit.** The sequence is decreasing because
each next level imposes more constraints. Let $b$ be its limit, and choose
a maximizing tuple $U^{(n)}$ and vector $\xi_n$ for each $n$. Evaluation
gives states on $C^*(F_m)$,

$$\varphi_n(a)=\langle\xi_n,a(U^{(n)})\xi_n\rangle.$$

The algebra is separable, so weak-star compactness of its state space gives
a subsequence converging to a state $\varphi$. In its GNS representation
$(\pi,\mathcal H,\xi)$, fix $r\in R$ and any word $q$. Once $n\geq|q|$,
the constraint gives

$$\varphi_n\big(q^*(r-1)^*(r-1)q\big)=0.$$

Passing to the limit shows $\pi(r-1)\pi(q)\xi=0$. The linear span of the
vectors $\pi(q)\xi$ is dense by cyclicity. Since $\pi(r-1)$ is bounded,
it vanishes on all of $\mathcal H$. This holds for every relator; therefore
$\pi$ factors through $C^*(G)$. Finally,

$$b=\varphi(f^*f)=\|\pi(f)\xi\|^2\leq\|f_G\|_{\max}^2.$$

Together with (5) this proves (4). $\square$

**Corollary 3.** If $w_G\ne1$, then $\beta_n(w-1)\geq2$ for every $n$,
and its limit is at least $2$, regardless of whether $w$ lies in the MF
radical.

**Proof.** The left regular representation and its vector $\delta_1$ give
$\|(w-1)\delta_1\|^2=2$. Apply (5). $\square$

There is no effective convergence rate in this proof. The dimension bound
is for this vector hierarchy only and must not be transferred to the global
norm hierarchy in the next section.

## 3. The global hierarchy has the MF radical as its word kernel

For $\delta>0$ instead put

$$\gamma_\delta(f)=\sup\left\{
 \|f(U)\|:
 d\geq1,\ U\in U(d)^m,\
 \max_{r\in R}\|r(U)-I\|\leq\delta
 \right\}. \tag{6}$$

The maximum over an empty relator set is zero. The feasible sets are again
nonempty; $\gamma_\delta(f)\leq\|f\|_{\ell^1(F_m)}$, and the values
decrease as $\delta\downarrow0$.

For a sequence of positive dimensions $d=(d_k)$ let
$\mathcal Q_d=\prod_kM_{d_k}/\bigoplus_kM_{d_k}$, where the direct sum
is the norm-zero ideal. Define

$$\nu(f)=\sup_{d,\,\rho:G\to U(\mathcal Q_d)}
\|\rho_*(f_G)\|, \tag{7}$$

with $\rho_*$ the linear extension of the group homomorphism to the group
algebra. Formula (7) is a seminorm defined here; it does not presume that
the full group C*-algebra is MF.

**Theorem 4.**

$$\lim_{\delta\downarrow0}\gamma_\delta(f)=\nu(f). \tag{8}$$

Consequently

$$w\in\operatorname{Rad}_{\mathrm{MF}}(G)
\quad\Longleftrightarrow\quad
\lim_{\delta\downarrow0}\gamma_\delta(w-1)=0. \tag{9}$$

**Proof: a near-maximizing sequence supplies a corona representation.**
Set $c=\lim_{\delta\downarrow0}\gamma_\delta(f)$. For each positive
integer $k$, choose a tuple $U^{(k)}$ with all relator norms at most $1/k$
and

$$\|f(U^{(k)})\|\geq\gamma_{1/k}(f)-1/k.$$

Such a choice is allowed by the definition of supremum; no finite-dimensional
attainment is assumed. The classes of the generator sequences are unitaries
in $\mathcal Q_d$, and each relator is the identity there. The presentation
therefore defines a homomorphism $\rho:G\to U(\mathcal Q_d)$. The quotient
norm of a bounded matrix sequence is its limsup norm, so

$$\|\rho_*(f_G)\|=\limsup_k\|f(U^{(k)})\|=c.$$

Thus $\nu(f)\geq c$.

**Proof: every corona representation has unitary lifts.** Fix a $\rho$ in
(7). A unitary class in $\mathcal Q_d$ has a bounded representative $x_k$
with $\|x_k^*x_k-I\|\to0$ and $\|x_kx_k^*-I\|\to0$. For sufficiently
large $k$, $x_k$ is invertible and its polar unitary

$$u_k=x_k(x_k^*x_k)^{-1/2}$$

satisfies $\|u_k-x_k\|\to0$. Put $u_k=I$ at the remaining finitely many
coordinates. This is a unitary representative of the same class. Apply this
separately to the finitely many generator images to obtain a unitary tuple
$U^{(k)}$ in every coordinate.

Every relator defect tends to zero, and the set $R$ is finite, so for each
$\delta>0$ all sufficiently large $k$ obey (6). Therefore

$$\|\rho_*(f_G)\|=\limsup_k\|f(U^{(k)})\|
\leq\gamma_\delta(f).$$

Let $\delta\downarrow0$ and then take the supremum over $\rho$ to get
$\nu(f)\leq c$. This proves (8).

For (9), the MF radical is equivalently the intersection of kernels of all
homomorphisms to norm matrix corona unitary groups. Indeed every MF target
embeds in such a unitary group, and the image of any homomorphism in (7) is
itself an MF group by the same definition. Thus $w$ belongs to this
intersection exactly when every norm $\|\rho(w)-I\|$ vanishes. Apply (8)
to $f=w-1$. $\square$

## 4. The precise remaining research step

| Tests imposed | Quantity optimized | Limit | Word kernel |
| --- | --- | --- | --- |
| Relators vanish on finitely many orbit vectors | $\beta_n(f)$, squared vector norm | $\|f_G\|_{\max}^2$ | Ordinary identity words |
| Relators are small on the whole matrix space | $\gamma_\delta(f)$, operator norm | $\nu(f)$ | MF radical for $f=w-1$ |

Theorem 2 closes the proposed escape of merely increasing the vector-context
depth. Theorem 4 states the genuinely needed global estimate exactly, but
does not prove it for a new nontrivial word. To advance the property-(T)-free
goal, one still has to show the right side of (9) vanishes for a specific
$w_G\ne1$ without importing the excluded rigidity argument.

The compactness proof in Theorem 2 yields representations on arbitrary
Hilbert spaces, including the regular representation. It gives neither
tracial matrix models nor a uniform operator-norm bound on relators. The
finite-dimensional compression of Lemma 1 is likewise not a global
approximate-representation construction. These distinctions are the reason
the two limits can have different word kernels.

## Provenance and verification scope

The finite simulation argument is in the classical setting of residual
finite-dimensionality of the free group's full C*-algebra. See
[Choi, *The full C*-algebra of the free group on two generators*,
Theorem 7 (1980)](https://msp.org/pjm/1980/87-1/pjm-v87-n1-p04-s.pdf).
The proofs above are given in full and do not claim a new proof of that
classical result as a breakthrough.

The normal-closure certificate and the integral Heisenberg finite-ball
witness have an independent exact-arithmetic replay in
[`experiments/finite_context_energy_audit.py`](../../experiments/finite_context_energy_audit.py).
That replay checks explicit finite data, not the compactness argument or
all presentations. The complete witness is
[`finite-context-heisenberg-witness.json`](finite-context-heisenberg-witness.json)
and the replay output is
[`finite-context-energy-replay.json`](finite-context-energy-replay.json).
The companion tests deliberately reject false word products and damaged
permutations. No Wolfram or Lean verification is claimed.
