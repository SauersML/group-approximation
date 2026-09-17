# The uniform critical l2 gap is a closed condition under local limits

Agent swarm-0917-w2-bs-pull-1, 2026-09-17, role transplanter, family
finite-models. Written for `fpbs-l2-gap-class-closed-under-local-limits`, on
the Benjamini–Schramm cone (`fpbs-benjamini-schramm-universal`, hole
`fpbs-pivotal-budget-universal`).

No computation is used. The only import is Duminil-Copin–Tassion (Section 1).
Everything else is proved here.

## 0. Setting and notation

* `G=(V,E)` is an infinite, connected, locally finite, vertex-transitive graph
  with root `o`. Cayley graphs of finitely generated groups are the main case.
* Bernoulli(`p`) bond percolation is `P^G_p`.
  - `tau^G_p(x,y) = P^G_p(x <-> y)`.
  - `tau^G_{p,R}(x,y)` is the probability that `x` and `y` are joined by an
    open path using only edges with both endpoints in the ball `B_R(o)`.
* `T^G_p` is the operator with kernel `tau^G_p`. Because the kernel is
  nonnegative,

      ||T^G_p|| := sup { <f, T^G_p g> / (||f||_2 ||g||_2) : f,g >= 0 finitely supported, nonzero }   (0.1)

  in `[1, infinity]`. When this is finite it is the `l2 -> l2` operator norm.
  Otherwise `T^G_p` is unbounded. Taking `f=g=1_{o}` shows `||T^G_p|| >= 1`.
* `p_c(G)` is the critical parameter.
  - `p_{2->2}(G) = sup{p : ||T^G_p|| < infinity}`.
  - `p_u(G) = inf{p : P^G_p`-a.s. there is exactly one infinite cluster`}`.
* **Local convergence.** `G_k -> G` means that for every `r` there is `k(r)`
  such that, for all `k >= k(r)`, the rooted ball `B_r(o_k)` in `G_k` is
  isomorphic to `B_r(o)` in `G`, as a rooted graph with all its edges.
  - Convergence of marked groups `(Gamma_k,S_k) -> (Gamma,S)` with a fixed
    number of generators is the special case of Cayley graphs.
  - Agreement of all relations of length at most `2r+1` gives the rooted-ball
    isomorphism.
* **Gap functionals.** For `M >= 1` put

      Gamma_M(G) := sup { p in [0,1] : ||T^G_p|| <= M },     g_M(G) := Gamma_M(G) - p_c(G).

  The set is nonempty because `||T_0|| = 1`.
* **The uniform gap class.** For `M >= 1` and `delta > 0`,

      U_{M,delta} := { G : ||T^G_{p_c(G)+delta}|| <= M },

  with `G` not in the class if `p_c(G)+delta > 1`.

Elementary facts used throughout:

* **(F1) Monotonicity.** `tau_p` is pointwise nondecreasing in `p`, so by (0.1)
  `p -> ||T_p||` is nondecreasing.
* **(F2) Left continuity.** `tau_p(x,y) = sup_R tau_{p,R}(x,y)`. Each
  `tau_{p,R}(x,y)` is a polynomial in `p` and nondecreasing. If `p_j` increases
  to `p`, then
  `sup_j tau_{p_j}(x,y) = sup_R sup_j tau_{p_j,R}(x,y) = sup_R tau_{p,R}(x,y) = tau_p(x,y)`.
* **(F3) Uniqueness makes the operator infinite.** Suppose there is a.s.
  exactly one infinite cluster at `p`. Then `theta(p) := P_p(o <-> infinity) > 0`:
  otherwise, by transitivity and a countable union, a.s. no vertex would lie in
  an infinite cluster. Two vertices in the unique infinite cluster are
  connected. So by Harris–FKG `tau_p(x,y) >= P_p(x<->inf, y<->inf) >= theta(p)^2`.
  Hence `<1_F, T_p 1_F> >= theta^2 |F|^2`, so `||T_p|| >= theta^2 |F|` for every
  finite `F`. `G` is infinite, so `||T_p|| = infinity`.
* **(F4) Supercritical susceptibility.** If `p > p_c(G)` then `theta(p) > 0` and
  `chi^G(p) := sum_y tau_p(o,y) = E_p|C(o)| >= theta(p) * infinity = infinity`.
  (Erratum, referee lens 2: the bound `tau_p(o,y) >= theta(p)^2` needs
  uniqueness and fails in the non-uniqueness phase, e.g. on `T_d`; the
  expectation bound above does not.) The truncated
  susceptibility `chi^G_r(p) := sum_{y in B_r(o)} tau_{p,r}(o,y)` increases to
  `chi^G(p)` as `r -> infinity` (monotone convergence).

## 1. Import: Duminil-Copin–Tassion

[DT] H. Duminil-Copin, V. Tassion, *A new proof of the sharpness of the phase
transition for Bernoulli percolation and the Ising model*, Comm. Math. Phys.
343 (2016) 725–745, arXiv:1502.03050v3. The e-print TeX source
`sharpnessPercoIsing-H.tex` was downloaded on 2026-09-17. Line numbers refer to
that file.

* Lines 265–266: "Let $G=(V,E)$ be a locally finite (vertex-)transitive
  infinite graph, together with a fixed origin $0\in V$."
* Lines 314–322: "$\tilde\beta_c:=\sup\{\beta\ge0: \varphi_\beta(S) <1\text{
  for some finite $S\subset V$ containing $0$} \}.$ In order to prove
  Theorem~\ref{thm:perco}, we show that Items~\ref{item:1}, \ref{item:2}
  and~\ref{item:3} hold with $\tilde{\beta_c}$ in place of $\beta_c$. This
  directly implies that $\tilde{\beta_c}=\beta_c$, and thus
  Theorem~\ref{thm:perco}."
* Lines 349–354, the nearest-neighbour form: "setting $J_{x,y}=0$ if
  $\{x,y\}\notin E$, $J_{x,y}=1$ if $\{x,y\}\in E$, and $p=1-e^{-\beta}$ ...
  $$\varphi_p(S)=p\sum_{x\in S}\sum_{\substack{y\notin S\\ \{x,y\}\in
  E}}\mathbb P_p[0\lr[S]x].$$"
  With these couplings, (eq:1) at line 309 is exactly this `varphi_p(S)`.
* Lines 398–412, the semicontinuity remark: "Consider the nearest-neighbor
  model. Since $\tilde{\beta_c}$ is defined in terms of finite sets, one can
  see that $\tilde{\beta_c}$ is lower semi-continuous when seen as a function
  of the graph in the following sense. Let $G$ be an infinite locally finite
  transitive graph. Let $(G_n)$ be a sequence of infinite locally finite
  transitive graphs such that the balls of radius $n$ around the origin in
  $G_n$ and $G$ are the same. Then, $\liminf \tilde\beta_c(G_n)\ge
  \tilde\beta_c(G)$. The equality $\beta_c=\tilde\beta_c$ implies that the
  semi-continuity \eqref{eq:4} also holds for $\beta_c$ [...] The discussion
  above shows that the hard part in the locality conjecture is the upper
  semi-continuity."

**Lemma 1.1 (lower semicontinuity of `p_c`).** If `G_k -> G` locally and all
graphs are infinite, locally finite and transitive, then
`liminf_k p_c(G_k) >= p_c(G)`.

*Proof.* This is the remark at lines 398–412. We rederive it from the
definition at lines 314–322, so that the passage to an arbitrary local
convergence rate is visible.

1. Let `p < p_c(G) = tilde p_c(G)`, where `p = 1-e^{-beta}` is increasing in
   `beta`. By definition of the supremum there are `p' > p` and a finite
   `S` containing `o` with `varphi_{p'}(S) < 1`.
2. `varphi_p(S)` is nondecreasing in `p`, since both the factor `p` and the
   connection probabilities inside `S` are. So `varphi_p(S) < 1`.
3. Choose `r` with `S` inside `B_r(o)`. Then `varphi_p(S)` depends only on the
   rooted ball `B_{r+1}(o)`.
4. For `k >= k(r+1)` the image `S_k` of `S` in `G_k` satisfies
   `varphi^{G_k}_p(S_k) = varphi^G_p(S) < 1`. So `p <= tilde p_c(G_k) = p_c(G_k)`.
5. Hence `liminf_k p_c(G_k) >= p` for every `p < p_c(G)`. QED.

## 2. Lower semicontinuity of the connectivity norm

**Theorem 2.1.** Let `G_k -> G` locally, where the `G_k` may also be finite.
For every `p in [0,1]`,

    ||T^G_p||  <=  liminf_k ||T^{G_k}_p||.                                  (2.1)

*Proof.*

1. Fix nonnegative `f`, `g` supported in `B_r(o)`, and fix `R >= r`.
2. For `k >= k(R)` let `phi_k : B_R(o_k) -> B_R(o)` be a rooted isomorphism.
   Put `f_k = f o phi_k` and `g_k = g o phi_k`, extended by `0`. These have the
   same `l2` norms as `f` and `g`.
3. The event "`x` and `y` are joined by an open path inside `B_R`" depends only
   on the edges of the rooted ball, and `phi_k` maps those edges bijectively.
   So for `x,y` in `B_r(o_k)`,
   `tau^{G_k}_{p,R}(x,y) = tau^G_{p,R}(phi_k x, phi_k y)`.
4. Therefore

       sum_{x,y} f(x) tau^G_{p,R}(x,y) g(y)
         = sum_{x,y} f_k(x) tau^{G_k}_{p,R}(x,y) g_k(y)
         <= <f_k, T^{G_k}_p g_k>
         <= ||T^{G_k}_p|| ||f|| ||g||.

5. Take `liminf_k`, then let `R -> infinity`. By monotone convergence
   `tau_{p,R} -> tau_p`, so
   `<f, T^G_p g> <= liminf_k ||T^{G_k}_p|| ||f|| ||g||`.
6. Take the supremum over `f` and `g` in (0.1). Finitely supported functions
   are exactly those supported in some `B_r(o)`. QED.

Transitivity is not used in this theorem.

**Remark (the inequality is strict in general).** Every finite graph has a
bounded operator, while a sequence of finite `d`-regular graphs with
`p > p_c(T_d)` has `||T^{G_k}_p|| -> infinity` (Proposition 4.1). The direction
of (2.1) is the only one available: the adjacency norm, the case `p` small, is
already only lower semicontinuous. Finite quotients of `F_2` converge to `F_2`
with adjacency norm `4`, while `F_2` has adjacency norm `2 sqrt 3`.

## 3. The uniform gap class is closed; `C_2` is `F_sigma`

**Theorem 3.1.** Let `G_k -> G` locally, all infinite, locally finite and
transitive, and let `M >= 1`.

* (a) `Gamma_M(G) >= limsup_k Gamma_M(G_k)`.
* (b) `g_M(G) >= limsup_k g_M(G_k)`, so `g_M` is upper semicontinuous.
* (c) `U_{M,delta} = {g_M >= delta}` is closed under local limits, for every
  `delta > 0`.
* (d) `C_2 := {G : p_c(G) < p_{2->2}(G)} = union over M in N and j in N of U_{M,1/j}`.
  So `C_2` is an `F_sigma` set in the space of transitive graphs, and in the
  space of `d`-marked groups.

*Proof.*

(a)
1. Let `p < limsup_k Gamma_M(G_k)`. Along a subsequence `k_j`,
   `Gamma_M(G_{k_j}) > p`.
2. By (F1), `||T^{G_{k_j}}_p|| <= M`.
3. Theorem 2.1 along the subsequence gives `||T^G_p|| <= M`, so
   `Gamma_M(G) >= p`.

(b) Using (a) and Lemma 1.1,

    g_M(G) = Gamma_M(G) - p_c(G) >= limsup Gamma_M(G_k) - liminf p_c(G_k) >= limsup (Gamma_M(G_k) - p_c(G_k)).

(c) First check that `{g_M >= delta}` equals `U_{M,delta}`.

* If `||T_{p_c+delta}|| <= M`, then `Gamma_M >= p_c + delta`.
* Conversely, suppose `Gamma_M >= p_c + delta`.
  - By (F1), `||T_p|| <= M` for every `p < p_c+delta`.
  - By (F2) and Fatou on finitely supported test functions,
    `||T_{p_c+delta}|| <= M`.
  - Also `p_c + delta < 1`, since `||T_1|| = infinity` on an infinite graph.

Closedness is then (b).

(d)
* If `||T_p|| < infinity` for some `p > p_c`, then `G` is in `U_{M,1/j}` for
  any integer `M >= ||T_p||` and any `j` with `1/j <= p - p_c`, using (F1).
* The converse inclusion is immediate. QED.

**Corollary 3.2 (transplant criterion for Benjamini–Schramm).** Let
`G_k -> G` locally, all infinite, locally finite and transitive. Suppose
there are `M < infinity` and `delta > 0` with `G_k` in `U_{M,delta}` for
infinitely many `k`. Then

    p_c(G) < p_c(G) + delta <= p_{2->2}(G) <= p_u(G),

so `p_c(G) < p_u(G)`. Also, on Cayley graphs, the pivotal budget holds with
bounded count on `[p_c(G), p_c(G)+delta]`:

    E_p[N_(n,R) | E_(n,R)] <= 2 d M^2.

*Proof.*

1. By Theorem 3.1(c), `||T^G_q|| <= M` at `q = p_c(G)+delta`.
2. By (F1) and (F3), there is no uniqueness at any `p <= q`. So `p_u(G) >= q`.
3. The pivotal bound is Theorem 4.1 of
   `research/artifacts/fpbs/docs/pivotal-kernel-ordering-2026-09-12.md`
   (`fpbs-l2-gap-gives-bounded-pivotal-counts`), with (F1). QED.

## 4. Where finite-model transplants die

The finite-models family would transplant a gap from approximants. Corollary
3.2 is the only transplant the operator route allows: it needs a common `M`
and a common `delta`. Here we show exactly which approximants can never supply
them.

**Proposition 4.1 (amenable and finite approximants carry no margin).** Let
`G` be infinite, locally finite and transitive. Let `G_k -> G` locally, where
each `G_k` is either finite and transitive, or infinite, transitive and
amenable. Then for every `M >= 1`,

    limsup_k Gamma_M(G_k) <= p_c(G).                                          (4.1)

So no choice of `M` and `delta > 0` has `G_k` in `U_{M,delta}` along the
sequence with the margin measured at `p_c(G)`. The operator transplant of
Corollary 3.2 certifies only `p_{2->2}(G) >= p_c(G)`, which is empty.

*Proof.*

1. **Row sums are a lower bound on these graphs.**
   * *Finite transitive `H`.* The matrix `tau^H_p` is symmetric and
     nonnegative, with constant row sum `chi^H(p)`. The all-ones vector is a
     Perron eigenvector, so `||T^H_p|| = chi^H(p) >= chi^H_r(p)` for every `r`.
   * *Infinite amenable transitive `H`.*
     - There are finite `F_j` with `|{x in F_j : B_r(x) not inside F_j}| / |F_j| -> 0`
       for each `r`. This is the Følner property applied to the `r`-boundary
       under bounded degree.
     - Then `<1_{F_j}, T_p 1_{F_j}> / |F_j| >= (1 - o(1)) chi^H_r(p)`, because
       `sum_{y in F_j} tau_p(x,y) >= chi^H_r(p)` whenever `B_r(x)` lies in `F_j`.
     - Here `chi_r` uses connections inside `B_r(x)`, which by transitivity
       have the same law at every `x`. So `||T^H_p|| >= chi^H_r(p)`.
2. **Truncated susceptibility is local.** `chi^H_r(p)` depends only on the
   rooted ball `B_r`.
3. **Contradiction above `p_c(G)`.**
   * Let `p > p_c(G)`. By (F4) there is `r` with `chi^G_r(p) > M`.
   * For `k >= k(r)`, `chi^{G_k}_r(p) = chi^G_r(p) > M`. So
     `||T^{G_k}_p|| > M`.
   * By (F1), `Gamma_M(G_k) <= p`.
4. Hence (4.1). QED.

**The invariant and the step where every member dies.**

* *The invariant.* The row-sum lower bound `||T_p|| >= chi_r(p)`. It holds
  exactly when the approximant has Følner-type sets at scale `r`, as finite
  and amenable graphs do. Combined with locality of `chi_r`, it pins
  `Gamma_M` of the approximants below `p_c(G) + o(1)`.
* *The step.* Every member dies at the uniform-margin step of Corollary 3.2.
* *What this kills.*
  - The glued-limit obstruction `fpbs-expander-approximant-giant-data-is-glued`
    is the giant-component shadow of the same fact.
  - This version needs no expansion hypothesis.
  - It covers every `p`.
  - It is quantitative for each `M`.

**Surviving approximants must be uniformly nonamenable in the percolation
sense.**

* By Theorem 3.1 the class that can still work is the closure of
  `U_{M,delta}` for fixed `(M, delta)`.
* Qualitative gap theorems do not supply fixed constants. Examples:
  - Hutchcroft `prop:criterion` together with Choi–Seo (Gamma1) and (Gamma2),
    in `fpbs-acylindrically-hyperbolic-critical-l2-gap`, which are limits as
    `p` increases to `p_c(G_k)`;
  - hyperbolicity with unbounded `delta`.
* The approximant constants may degenerate, and a limit such as a free Burnside
  group, which is not acylindrically hyperbolic, is then not reached.
* Classes whose certificates are themselves local and closed, such as
  `||A||`-type bounds and free products on union generating sets, reach only
  their own closure. For example, the balls of a free product on a union
  generating set are determined by the factor balls, so the limit of
  `A_k * B_k` is `A * B` with `A = lim A_k` and `B = lim B_k`.

## 5. Decomposition recorded

For a nonamenable Cayley graph `G` outside the known `C_2` classes:

    BS(G)  <==  [D1] a local approximation G_k -> G by infinite transitive graphs
              + [D2] one M with ||T^{G_k}_{q_k}|| <= M for all large k
              + [D3] one delta > 0 with q_k >= p_c(G_k) + delta.

* [D3] can be replaced by `q_k >= p_c(G) + delta`, with no locality input.
  - Then (F1) gives `||T^{G_k}_{p_c(G)+delta}|| <= M`, and Theorem 2.1 passes
    this to `G`.
  - By Lemma 1.1, the original [D3] with `delta` implies this form with
    `delta/2` for large `k`.
* Each prerequisite can fail on its own:
  - [D1] is always available, for instance `G_k = G`, but it is useless unless
    the approximants lie in a certified class.
  - [D2] fails for finite and amenable approximants (Proposition 4.1).
  - [D3] is exactly where qualitative theorems stop.
* The decomposition is sharp: `G` is in `C_2` if and only if the constant
  sequence satisfies [D1]–[D3].

## 6. Pivotal budget remark (ball-locality)

`E_p[N_(n,R) | E_(n,R)]` depends only on the rooted ball `B_R`, because the
walk law `mu^n` is supported in `B_n`. So any statement "`E_p[N|E] <= C n` for
all `n`, all `R >= n` and all `p` in `[q, p0]`", with fixed `(C, q, p0)`, passes
from the approximants to the limit.

It does not by itself transplant PB. PB starts at `p_c(G)`, and Lemma 1.1 gives
only `p_c(G) <= liminf p_c(G_k)`. So the approximants would need the budget
below their own critical points, a regime where PB has not been studied.
