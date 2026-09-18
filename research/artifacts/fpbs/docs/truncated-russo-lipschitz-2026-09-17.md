# Truncated Russo–Lipschitz bounds and the chemical form of (IS)

Author: swarm worker b-p-bs1 (wave swarm-0917), role transplanter,
family symbolic-dynamics. Date: 2026-09-17. Status: complete written proofs
of Theorems 1 and 2 and Corollary 3. No computation is used.

## 0. Setting and notation

* `G` is a nonamenable Cayley graph of a finitely generated group with
  symmetric generating set `S` and degree `d=|S|`. `mu` is the simple random
  walk step law, `X_n` the walk from `e`, and `rho<1` its spectral radius.
* `P_p` is Bernoulli(`p`) bond percolation, independent of the walk. `d_omega`
  is the chemical (intrinsic) distance in the open subgraph, with
  `d_omega(u,v)=infinity` when `u` and `v` are not connected.
* `a_n(p)=E P_p(e <-> X_n)` and `lambda(p)=lim_n a_n(p)^(1/n)=sup_n a_n(p)^(1/n)`.
  The limit exists by FKG supermultiplicativity (`fpbs-integrated-pivotal-rate-identity`).
* Schramm's lemma (`fpbs-critical-walk-correlation`, Hutchcroft 1804.10191
  Prop 6.4) gives `a_n(p_c) <= rho^n`, and `lambda(p_c)=rho`
  (`fpbs-integrated-pivotal-rate-identity`).
* **Truncated connection.** For a real `L>=1`, `x` in `G` and `M>=0`, let
  `A_(x,M)={d_omega(e,x)<=M}`. Define

      a^(L)_n(p) = E P_p(A_(X_n, Ln)) = P_p(d_omega(e,X_n) <= L n).

* (IS) is the statement `lambda(p) -> rho` as `p` decreases to `p_c`
  (`fpbs-integrated-sensitivity-universal`).

## 1. The truncated Russo–Lipschitz inequality

**Lemma 1.1.** For every `x`, every `M>=0` and every `0<q<=p<=1`,

    P_p(A_(x,M)) <= (p/q)^M P_q(A_(x,M)).

*Proof.* If `|x|>M` both sides vanish. Otherwise `A=A_(x,M)` is an increasing
event determined by the finitely many edges of the ball `B_M(e)`, so
`f(p)=P_p(A)` is a polynomial with `f>0` on `(0,1]`. By Russo's formula,
`f'(p)=sum_g P_p(g pivotal for A)`, where pivotality does not depend on the
state of `g`. Hence `P_p(g pivotal)=p^(-1) P_p(g pivotal and open)`, and
`{g pivotal and open}` is contained in `A`. So

    f'(p) = p^(-1) E_p[ #(open pivotal edges for A) ; A ].

On `A` fix one open path `gamma` from `e` to `x` of length at most `M`.
Closing an open pivotal edge destroys `A`, so every open pivotal edge lies on
`gamma`. So the count is at most `M` on `A`, and `f'(p) <= M f(p)/p`.
Integrating `(log f)' <= M/p` from `q` to `p` gives the claim. `QED`

The load-bearing step is that a truncated increasing event has at most as
many open pivotal edges as the length of the certificate. This is the only
place where the pivotal budget (PB) is "free": PB holds with `C=L` for the
truncated events. PB is load-bearing only for the untruncated events.

## 2. Theorem 1 (truncated walk rates are log-Lipschitz)

**Theorem 1.** Let `L>=1`.

1. `lambda_L(p)=lim_n a^(L)_n(p)^(1/n)` exists and equals `sup_n a^(L)_n(p)^(1/n)`.
   It lies in `[p,1]`.
2. For `0<q<=p<=1`: `lambda_L(q) <= lambda_L(p) <= (p/q)^L lambda_L(q)`. In
   particular `lambda_L` is continuous on `(0,1]`.
3. For `p>=p_c`: `lambda_L(p) <= rho (p/p_c)^L`.
4. `lambda_L(p)` is nondecreasing in `L`, and `sup_L lambda_L(p) = lambda(p)`
   for every `p`.

*Proof.* (1) Positivity: if all `n` edges traversed by the walk trajectory are
open, then `d_omega(e,X_n)<=n<=Ln`. So `a^(L)_n(p) >= p^n`.
Supermultiplicativity: write `X_(n+m)=X_n Y_m`, where `Y` is an independent
copy of the walk. Conditionally on the walks, the events `A_(X_n,Ln)` and
`X_n . A_(Y_m,Lm)` (the translate) are increasing, and their intersection
lies in `A_(X_(n+m), L(n+m))` by the triangle inequality for `d_omega`. By
Harris–FKG and translation invariance,
`P_p(A_(X_(n+m),L(n+m)) | X,Y) >= P_p(A_(X_n,Ln) | X) P_p(A_(Y_m,Lm) | Y)`.
Taking expectations and using independence of `X_n` and `Y_m` gives
`a^(L)_(n+m) >= a^(L)_n a^(L)_m`. Fekete's lemma gives the limit and the
supremum formula. Also `a^(L)_n <= 1`.

(2) Monotonicity in `p` holds since `A_(x,M)` is increasing. For the upper
bound, apply Lemma 1.1 with `M=Ln` for each `x`, average over `X_n`, take
`n`-th roots and let `n -> infinity`. Continuity follows because
`log lambda_L` is monotone and Lipschitz in `log p` with constant `L`.

(3) Apply (2) with `q=p_c` and use `a^(L)_n(p_c) <= a_n(p_c) <= rho^n`
(Schramm's lemma).

(4) Monotonicity in `L` holds since `A_(x,Ln)` increases with `L`. For each
fixed `n`, `A_(X_n,Ln)` increases to `{e <-> X_n}` as `L -> infinity`, so
`a^(L)_n -> a_n` by monotone convergence. Hence

    sup_L lambda_L = sup_L sup_n (a^(L)_n)^(1/n) = sup_n sup_L (a^(L)_n)^(1/n)
                   = sup_n a_n^(1/n) = lambda.   QED

*Sanity checks.*

* `L=1`, `p=1`: `lambda_1(1)=1`, since `|X_n|<=n`. (3) then reads `p_c<=rho`.
  This is consistent with the trivial bound `a_n(p_c) >= p_c^n`.
* Taking `L` just above the speed `s` of the walk at `p=1` gives `p_c^s<=rho`.
  This is consistent with `a_n(p_c) >= E p_c^(|X_n|)`.
* On the 3-regular tree: `p_c=1/2`, `rho=2 sqrt 2/3`, `s=1/3`, and
  `rho^3 = 0.838 >= 1/2`.

**Remark (the only lsc/usc point).** `lambda` is a supremum of the continuous
functions `lambda_L`, so it is lower semicontinuous. This is all that Fekete
gives. (IS) is right-continuity at `p_c`, which is exactly a failure of
uniformity of `lambda_L -> lambda` near `p_c`. Theorem 2 makes this precise
with the explicit scale.

## 3. Theorem 2 ((IS) is equivalent to sub-mean-field chemical saturation)

**Definition (SE).** `G` has *sub-scale chemical saturation* if there are
slopes `L(epsilon)>=1`, for `epsilon>0` small, with

    epsilon L(epsilon) -> 0   and   lambda_(L(epsilon))(p_c+epsilon) / lambda(p_c+epsilon) -> 1
    as epsilon -> 0.

**Theorem 2.** For every nonamenable Cayley graph, (IS) holds if and only if
(SE) holds.

*Proof.* (SE) implies (IS). By Theorem 1(3),
`lambda_(L(epsilon))(p_c+epsilon) <= rho (1+epsilon/p_c)^(L(epsilon)) <= rho exp(epsilon L(epsilon)/p_c)`,
which tends to `rho`. Divide by the ratio, which tends to 1. This gives
`limsup lambda(p_c+epsilon) <= rho`. Monotonicity and `lambda(p_c)=rho` give
the matching lower bound.

(IS) implies (SE). Choose `L(epsilon)=max(1, epsilon^(-1/2))`. Then
`epsilon L(epsilon) -> 0` and `L(epsilon) -> infinity`. By monotonicity in
`p` and Theorem 1(4) at `p_c`,
`lambda_(L(epsilon))(p_c+epsilon) >= lambda_(L(epsilon))(p_c) -> lambda(p_c) = rho`.
By (IS), `lambda(p_c+epsilon) -> rho`. Since `rho>0`, the ratio tends to 1
(it is at most 1 by Theorem 1(4)). `QED`

**Quantitative form.** Let `Delta = lim_(epsilon -> 0) log(lambda(p_c+epsilon)/rho) >= 0`.
The limit exists by monotonicity, and (IS) says `Delta=0`. Theorem 1(3) shows
that every slope `L < p_c Delta / epsilon` has
`lambda_L(p_c+epsilon) <= rho exp(epsilon L / p_c) < rho e^Delta <= lambda(p_c+epsilon)`.
So if (IS) fails with jump `Delta`, the exponential rate of walk connections at
`p_c+epsilon` is carried entirely by open paths of chemical slope at least
`p_c Delta/epsilon`.

## 4. Corollary 3 (forced chemical stretch in the uniqueness phase)

**Corollary 3.** Let `t` be a parameter with `theta(t)>0` at which the infinite
cluster is a.s. unique. Then for every `L>=1` and `n`,

    P_t( d_omega(e,X_n) <= L n | e <-> X_n ) <= theta(t)^(-2) rho^n (t/p_c)^(L n).

So this conditional probability decays exponentially whenever
`L < log(1/rho)/log(t/p_c)`, and in particular whenever `L < p_c log(1/rho)/(t-p_c)`.

*Proof.* Harris–FKG and uniqueness give `P_t(e <-> x) >= theta(t)^2`. The
numerator is `a^(L)_n(t)`, which is at most `(t/p_c)^(Ln) a_n(p_c) <= (t/p_c)^(Ln) rho^n`
by Lemma 1.1 and Schramm's lemma. `QED`

**Consequence for the collapse scenario.** If `p_c=p_u`, then Corollary 3
applies at every `t=p_c+epsilon`. Walk-typical connections at `p_c+epsilon`
then have chemical slope at least `p_c log(1/rho)/epsilon`, except on an
exponentially small event. This is exactly the heuristic mean-field
intrinsic correlation scale `1/epsilon`, with the explicit constant
`p_c log(1/rho)`. So the collapse scenario is *not* contradicted by chemical
stretch at that scale. Any proof of BS or (IS) through chemical distance must
show that slopes `o(1/epsilon)` already saturate the rate (SE), or that the
stretch constant is beaten.

## 5. What this kills and what it isolates

1. **Russo on truncated events gives no information about (IS).** Lemma 1.1
   and Theorem 1 hold on *every* nonamenable Cayley graph, including any
   hypothetical collapse graph. Truncated rates at slopes `L <= K/epsilon`
   are bounded by `rho exp(K/p_c)`, and truncated rates at slopes
   `o(1/epsilon)` tend to `rho` unconditionally. So a pivotal argument that
   only uses path-length bounds on pivotal counts (the truncated PB, with
   `C=L`) proves a statement that holds under collapse, and cannot yield (IS)
   or BS. Such an argument must add the *comparison* `lambda_L ~ lambda` at
   a sub-scale slope, which is exactly (SE).
2. **Isolated prerequisite.** (IS) is equivalent to (SE): exponential-rate
   domination of near-critical walk connections by chemically short paths at
   slope `o(1/epsilon)`. (IS) implies BS through
   `fpbs-integrated-sensitivity-universal` and the Section 6 chain of the
   pivotal-kernel ordering. So BS reduces to a chemical-distance statement
   *strictly below* the mean-field intrinsic correlation scale, while
   Corollary 3 shows that the collapse must live *at or above* that scale.
3. **Relation to the intrinsic-radius decomposition** (swarm-0917 w5,
   `fpbs-intrinsic-l2-rate-closed-zero-set`, not yet on this tip). That node
   studies `l2->2` rates of intrinsic-radius kernels and proves qualitative
   stretch divergence at `p_c+`. The present note works with walk-averaged
   rates, gives the explicit log-Lipschitz constant `L` and the explicit slope
   `p_c log(1/rho)/epsilon`, and proves an *equivalence* with (IS) rather than
   a one-way reduction through uniform chemical stretch above `p_u`.
