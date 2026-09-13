# Pivotal kernels for Benjamini--Schramm: ordering, bounded counts under the critical L2 gap, and the estimate that fails

Date: 2026-09-12. Status: written proofs, not Lean verification. This note
does NOT prove the Benjamini--Schramm conjecture
(`fpbs-benjamini-schramm-universal`), and it proves none of the four pivotal
kernels universally. It gives no new class of Cayley graphs with `p_c<p_u`.
What it does:

* It orders the four OPEN kernels by logical strength and proves each
  implication it uses (Section 3):

      PB  ==>  IS  ==>  NC  ==>  BS,        PB  ==>  RATE  ==>  BS.

  Neither IS nor NC is known to imply RATE, or conversely. None of the
  strict inequalities is proved: no graph is known on which one kernel holds
  and another fails.
* It proves a bounded pivotal count from an L2 hypothesis (Theorem 4.1):
  on every Cayley graph, for both walks, all `n>=1`, `R>=n` and `p`,

      E_p[N_(n,R) | E_(n,R)] <= 2 d ||T_p||_(2->2)^2.

  So every nonamenable Cayley graph with `p_c<p_(2->2)` satisfies all four
  kernels, and satisfies PB with a count bounded independently of `n`
  (Corollary 4.2).
* It checks every kernel on graphs where `p_c<p_u` is known: regular trees,
  Cayley graphs of hyperbolic groups, and Cayley graphs whose automorphism
  group has a quasi-transitive nonunimodular subgroup (for example
  `T_k x Z^m`). No kernel fails on any of them, so no obstruction is landed
  (Section 5).
* It names the estimate that a universal proof by this method needs, and
  shows why that estimate fails in general (Section 6). It is infinite at every
  uniqueness parameter, so it certifies nonuniqueness and cannot be used to
  derive it.

Before this note, the only kernel-level verification in the archive was the
cactus theorem (`fpbs-cactus-finite-ball-pivotal-budget`).

## 1. Setup and the four kernels

Let `G=Cay(Gamma,S)` with `S` finite, symmetric, and excluding the identity
`e`, and let `d=|S|`. Suppose `G` is nonamenable, write `c=p_c(G)`, and use
independent Bernoulli bond percolation. Write

    tau_p(x,y) = P_p(x connected to y),      tau_p(x) = tau_p(e,x).

Invariance gives `tau_p(x,y)=tau_p(x^(-1)y)`, and `tau_p(x)=tau_p(x^(-1))`.
For nonnegative functions on `Gamma` use the convolution
`(f*g)(x) = sum_y f(y) g(y^(-1)x)`; all sums below have nonnegative terms, so
Tonelli justifies every rearrangement. Right convolution by `tau_p` is the
operator `T_p` of [H, Section 2], and

    p_(2->2) = sup{ p : ||T_p||_(2->2) < infinity },
    p_c <= p_(2->2) <= p_u                              [H, quoted in 5.1].

**Walks.** A step law `mu` is either the simple walk `mu_S = d^(-1) 1_S` or
the lazy walk `mu_L = (delta_e + mu_S)/2`. Let `X_n` be the product of `n`
independent steps, independent of the percolation, and let `mu^n` be its law.
Let `rho_S`, `rho_L` be the `l2` operator norms of the two walks, so
`rho_L=(1+rho_S)/2` and `lambda_0=-log rho_L>0`. Kesten's theorem gives
`rho_S<1`.

For `R>=n`, let `E_(n,R)` be the event that `e` connects to `X_n` inside the
induced ball `B_R`, and set `a_(n,R)(p)=P_p(E_(n,R))`. Let `N_(n,R)` be the
number of open edges pivotal for this connection on `E_(n,R)`. Expectations
include the walk. Let `a_n(p)=lim_R a_(n,R)(p)=E tau_p(X_n)`. Finite Russo
differentiation (`exploration.md` (2.2), `exploration-pivotal-projections.md`
(6.3)) gives

    d/dp log a_(n,R)(p) = E_p[N_(n,R) | E_(n,R)] / p.          (1.1)

The kernels, as stated on the tip:

* **(PB)** `fpbs-pivotal-budget-universal`: there are `C` and `p0 in (c,1)`
  with `E_p[N_(n,R)|E_(n,R)] <= Cn` for all `n>=1`, `R>=n` and `p in [c,p0]`.
* **(IS)** `fpbs-integrated-sensitivity-universal`, projections (IS), simple
  walk:
  `lim_(eps->0) lim_n lim_R n^(-1) int_c^(c+eps) E_s[N_(n,R)|E_(n,R)] ds/s = 0`.
* **(NC)** `fpbs-pivotal-nonconcentration-universal`, exploration Proposition 3,
  lazy walk: `B(eps) < -log rho_L` for some `eps>0`, where
  `B(eps)=limsup_n lim_R M_(n,R)(c+eps)` and
  `M_(n,R)(t) = n^(-1) int_c^t E_p[N_(n,R)|E_(n,R)] dp/p`.
* **(RATE)** `fpbs-universal-subcritical-pivotal-growth-rate`, spectral-spike
  Corollary 6.2, lazy walk: some `p0 in (c,1)` has
  `limsup_n n^(-1) log(1+L_n(p0)) < lambda_0/2`, where
  `L_n(p0) = sup_(R>=n) sup_(c<=p<=p0) n^(-1) E_p[N_(n,R)|E_(n,R)]`.

The PB node does not name its walk. Every positive result below is proved for
both walks, so this ambiguity does not affect any verification. For the
ordering, PB with the simple walk implies PB with the lazy walk with the same
constant. Indeed `X^L_n = X^S_(K_n)` with `K_n ~ Bin(n,1/2)`, and the event and
the pivotal count depend only on the endpoint, so

    E[N^L_(n,R); E^L_(n,R)] = sum_k P(K_n=k) E[N^S_(k,R); E^S_(k,R)]
                            <= C n sum_k P(K_n=k) a^S_(k,R) = C n a^L_(n,R),

using `R>=n>=k` and `N=0` when `k=0`. So reading PB with the lazy walk is the
weaker, and therefore safe, choice.

## 2. Rates: existence, walk transfer, critical value

**Lemma 2.1.** For either walk and `p in (0,1]`, the limit
`lambda(p) = lim_n a_n(p)^(1/n)` exists, equals `sup_n a_n(p)^(1/n)`, is
nondecreasing in `p`, and satisfies `rho <= lambda(p) <= 1`.

*Proof.* By positive association and invariance,
`tau_p(xy) >= tau_p(x) tau_p(y)`. Averaging over independent increments gives
`a_(n+m) >= a_n a_m`. Moreover `a_n>0`: the walk's own edges are open with
probability at least `p^n`. Fekete's lemma gives the limit and the supremum
formula. Monotonicity in `p` is inherited from `a_n`. Since
`a_n(p) >= mu^n(e)`, the return-probability formula gives `lambda >= rho`
(along even `n` for the simple walk). QED. (This is projections 6.1 for the
simple walk; the lazy case is identical.)

**Lemma 2.2 (walk transfer).** `lambda_L(p) = (1+lambda_S(p))/2`.

*Proof.* `a^L_n = E a^S_(K_n)`. From `a^S_k <= lambda_S^k` (supremum formula),
`a^L_n <= ((1+lambda_S)/2)^n`. Given `eta>0`, there is `c_eta>0` with
`a^S_k >= c_eta (lambda_S-eta)^k` for all `k`, since the limit holds and every
`a^S_k>0`. Then `a^L_n >= c_eta ((1+lambda_S-eta)/2)^n`. QED.

**Lemma 2.3 (critical value).** `lambda_S(c)=rho_S` and `lambda_L(c)=rho_L`.

*Proof.* [H, Proposition 6.4] (quoted in 5.1) gives `a^S_n(p) <= rho_S^n` for
`0<=p<=p_(2->2)`, and `c<=p_(2->2)`. Combine with Lemma 2.1, then Lemma 2.2.
QED. This is (6.2) of the projections note, recorded as
`fpbs-integrated-pivotal-rate-identity`.

**Lemma 2.4 (rate identity, both walks).** For `c<t<=1`,

    lim_n lim_R n^(-1) int_c^t E_p[N_(n,R)|E_(n,R)] dp/p = log(lambda(t)/rho).

*Proof.* By (1.1), the integral is `n^(-1) log(a_(n,R)(t)/a_(n,R)(c))`. As
`R->infinity`, both probabilities increase to positive limits. Then apply
Lemmas 2.1 and 2.3. QED. In particular `B(eps) = log(lambda_L(c+eps)/rho_L)`,
and the `limsup` defining `B` is a limit.

## 3. The ordering

**Proposition 3.1 (PB implies IS).** Assume PB, lazy walk, with constants
`C, p0`. For `0<eps<=p0-c`, integrating (1.1) over `[c,c+eps]` gives

    log a_(n,R)(c+eps) - log a_(n,R)(c) <= C n log(1+eps/c).

Let `R->infinity`, take `n`-th roots, and let `n->infinity`. Lemma 2.3 gives
`lambda_L(c+eps) <= rho_L (1+eps/c)^C`, and Lemma 2.1 gives
`lambda_L >= rho_L`. So `lambda_L(c+eps) -> rho_L`. By Lemma 2.2,
`lambda_S(c+eps) = 2 lambda_L(c+eps) - 1 -> rho_S`, and by Lemma 2.4 for the
simple walk the IS integral tends to `log 1 = 0`. QED. If PB is read with the
simple walk, the same argument runs without the transfer. This is the
remark of projections Section 6.2, with its walk conventions made precise.

**Proposition 3.2 (IS implies NC).** By Lemma 2.4 for the simple walk, IS is
the statement `lambda_S(c+eps) -> rho_S`. By Lemma 2.2,
`lambda_L(c+eps) -> rho_L`. By Lemma 2.4 for the lazy walk,
`B(eps) -> 0`. Since `-log rho_L = lambda_0 > 0`, some `eps` has
`B(eps) < -log rho_L`. QED.

**Proposition 3.3 (PB implies RATE).** PB gives `L_n(p0) <= C`, so
`n^(-1) log(1+L_n(p0)) -> 0 < lambda_0/2`. QED.

**The implications into BS.** NC implies BS is exploration Proposition 3
(`fpbs-pivotal-nonconcentration-implies-nonuniqueness`). Its proof was re-read
for this note: `limsup_n n^(-1) log a_n(c+eps) = log rho + B(eps) < 0`
contradicts `a_n >= theta^2` under uniqueness. RATE implies BS is
`fpbs-universal-pivotal-rate-contradiction-route` through spectral-spike
Theorem 6.1, whose mean-value argument was also re-read. The results of
Sections 4 and 5 do not use either implication.

**What is not proved.**

* *IS or NC versus RATE.* IS bounds an integral over parameters. RATE bounds a
  supremum over parameters and radii. A pointwise spike of height
  `exp(beta n)`, with `beta >= lambda_0/2`, on a parameter window of width
  `exp(-2 beta n)` is formally compatible with IS and violates RATE.
  Conversely, RATE allows `E[N|E]` of order `n exp(alpha n)` throughout
  `[c,p0]`, whose integral over `[c,c+eps]` is unbounded in `n`. These are
  compatibility statements about functions, not percolation models, so
  neither non-implication is proved either.
* *Strictness.* On every graph where any kernel has been verified (cacti, and
  the class of Corollary 4.2), PB holds, and so all four hold.

So the weakest kernels are NC and RATE, which are incomparable as far as is
known. PB is the strongest.

## 4. Bounded pivotal counts under the critical L2 gap

Write `A=1_S`, `||.||` for the operator norm on `l2(Gamma)`, and
`T_p f = f*tau_p`. Since `tau_p` is symmetric,
`(T_p f)(x) = sum_y tau_p(x,y) f(y)`, which is the operator of [H, Section 2].
Put

    W_n(p) = sum_x mu^n(x) (tau_p*A*tau_p)(x)   in [0,infinity].

**Theorem 4.1.** Let `G=Cay(Gamma,S)` be any Cayley graph, `d=|S|`,
`p in (0,1)`, `n>=1` and `R>=n`. For either walk:

* (a) `E_p[N_(n,R); E_(n,R)] <= p W_n(p)`.
* (b) For all `m,m'>=0` with `m+m'=n`,
  `W_n(p) <= d ||T_p||^2 (mu^(2m)(e) mu^(2m')(e))^(1/2)`.
* (c) Lazy walk: `E_p[N_(n,R)|E_(n,R)] <= sqrt(2) p d ||T_p||^2`.
  Simple walk: `E_p[N_(n,R)|E_(n,R)] <= max(pd, sqrt(d)) ||T_p||^2`.

So `E_p[N_(n,R)|E_(n,R)] <= 2 d ||T_p||^2` for both walks. The bound is
empty when `||T_p||=infinity`. It does not depend on `n` or `R`.

*Proof of (a).* Condition on `X_n=x`. An open edge `f` pivotal for
`E_(n,R)` lies on a simple open path from `e` to `x` in `B_R`. The path crosses
`f` once, say from `u` to `v`. Its two pieces witness `{e<->u in B_R}` and
`{v<->x in B_R}` on edge sets disjoint from each other and from `f`. So

    P_p(f open and pivotal) <= sum_(orientations (u,v) of f)
                               P_p({e<->u} o {f open} o {v<->x}),

where `o` is disjoint occurrence of increasing events on the finitely many
edges of `B_R`. By the BK inequality and monotonicity in the volume, each term
is at most `tau_p(u) . p . tau_p(v^(-1)x)`. The pairs `(u,us)` with `s in S`
enumerate every oriented edge exactly once, so

    E_p[N_(n,R); E_(n,R) | X_n=x]
      <= p sum_u sum_(s in S) tau_p(u) tau_p((us)^(-1) x)
       = p (tau_p*A*tau_p)(x).

Average over `x`. QED

*Proof of (b).* For nonnegative `F,G` on `Gamma`, write `G^v(x)=G(x^(-1))`.
Then `sum_x F(x)G(x) = (F*G^v)(e)` and `(F*G)(e) = (G*F)(e)`, with values in
`[0,infinity]`. The functions `mu^j`, `tau_p` and `A` are symmetric, and so is
`tau_p*A*tau_p`. Hence

    W_n = (mu^m * mu^(m') * tau_p * A * tau_p)(e)
        = (mu^(m') * tau_p * A * tau_p * mu^m)(e)
        = < mu^(m') * tau_p ,  mu^m * tau_p * A >.

Right convolution by `A` is a sum of `d` right translations, so its norm is at
most `d`. Also `||mu^j||_2^2 = mu^(2j)(e)`. By Cauchy--Schwarz,

    W_n <= ||T_p|| mu^(2m')(e)^(1/2) . d ||T_p|| mu^(2m)(e)^(1/2).   QED

*Proof of (c).* The event `E_(n,R)` holds when `X_n=e`, so
`a_(n,R) >= mu^n(e)`.

*Lazy walk.* Right convolution by `mu_L=(delta_e+mu_S)/2` is self-adjoint
with spectrum in `[0,1]`. So by the spectral theorem
`mu_L^j(e) = <delta_e*mu_L^j, delta_e>` is nonincreasing in `j`. Also
`mu_L^j(e) >= mu_L^(j-1)(e) mu_L(e) = mu_L^(j-1)(e)/2`.

* For even `n`, take `m=m'=n/2`. Then `W_n <= d||T_p||^2 mu^n(e)`.
* For odd `n`, take `m=(n-1)/2` and `m'=(n+1)/2`. Then
  `mu^(n-1)(e) mu^(n+1)(e) <= 2 mu^n(e) . mu^n(e)`, so
  `W_n <= sqrt(2) d ||T_p||^2 mu^n(e)`.

Divide (a) by `a_(n,R) >= mu^n(e)`.

*Simple walk, even `n`.* The same choice gives `E[N|E] <= p d ||T_p||^2`.

*Simple walk, odd `n`.* Here `mu_S^n(e)` may vanish. But `E_(n,R)` also holds
when `X_n in S` and the edge `{e,X_n}` is open. That edge lies in `B_R`
because `R>=1`. So

    a_(n,R) >= p sum_(s in S) mu_S^n(s) = p d mu_S^(n+1)(e) > 0.

Take `m=(n-1)/2` and `m'=(n+1)/2`. Since `mu_S^2(e)=1/d`,
`mu_S^(n-1)(e) <= d mu_S^(n+1)(e)`. Thus

    E[N|E] <= p d ||T_p||^2 (mu_S^(n-1)(e) mu_S^(n+1)(e))^(1/2)
              / (p d mu_S^(n+1)(e))
           <= sqrt(d) ||T_p||^2.

Finally `sqrt(2) p d <= 2d` and `max(pd, sqrt d) <= d`. QED

**Corollary 4.2.** Let `G` be a nonamenable Cayley graph with
`p_c<p_(2->2)`. Fix `p0 in (c, p_(2->2))` and put `C_0 = 2d||T_(p0)||^2`.

`C_0` is finite. For nonnegative kernels the operator norm is monotone in the
kernel, and `tau_p` is pointwise nondecreasing in `p`. Also some `p1>p0` has
`||T_(p1)||<infinity`.

Then, for both walks, all `n>=1`, `R>=n` and `p in (0,p0]`,

    E_p[N_(n,R) | E_(n,R)] <= C_0.                                  (4.1)

Consequently:

* (i) PB holds with `C=C_0` and this `p0`, in the stronger form of a count
  bounded independently of `n`.
* (ii) RATE holds, since `L_n(p0) <= C_0/n`.
* (iii) IS and NC hold, by Propositions 3.1 and 3.2.
* (iv) For `eps<=p0-c`, `M_(n,R)(c+eps) <= C_0 n^(-1) log(1+eps/c)`, so
  `B(eps)=0`.

QED. Item (iv) also follows directly from [H, Proposition 6.4], which gives
`lambda(p)=rho` for `p<=p_(2->2)`. None of this gives a new graph with
`p_c<p_u`, because `p_(2->2)<=p_u` [H] (quoted in 5.1). What is new is that
the four kernels hold, and PB holds with a bounded count, on this class.

## 5. Test graphs where `p_c<p_u` is known

### 5.1 Sources, quoted from the TeX source

[H] is Tom Hutchcroft, *Percolation on Hyperbolic Graphs*, arXiv:1804.10191.
It was read from its TeX source on MSI. Line numbers refer to that source;
markup is transcribed.

* Line 298: "In particular, p_c(G)=p_{1→1}(G)=p_{∞→∞}(G) ≤ p_{q→q}(G) ≤
  p_{2→2}(G) for every quasi-transitive graph G and q∈[1,∞]."
* Line 301: "If G is quasi-transitive and G[p] has a unique infinite cluster,
  then the two-point function τ_p(u,v) ≥ P_p(u→∞)P_p(v→∞) is bounded below by
  a positive constant, and it follows that p_{q→q}(G) ≤ p_u(G) whenever
  q∈[1,∞] and G is infinite and quasi-transitive."
* `thm:pell2` (label line 304, statement line 305): "Let G be a connected, locally finite,
  quasi-transitive, nonamenable, Gromov hyperbolic graph. Then
  p_c(G)<p_{q→q}(G) for every q∈(1,∞)."
* `thm:nonunimodular` (label line 551, statement line 552): "Let G be a connected, locally finite graph,
  and suppose that Aut(G) has a quasi-transitive nonunimodular subgroup. Then
  p_c(G)< p_{q→q}(G) for every q∈(1,∞)."
* Proposition 6.4 (label `prop:nonuniquenessatpell2` line 1721, statement from
  line 1722): "Let G be a
  connected, locally finite, transitive, nonamenable graph, let X be simple
  random walk on G, and let ρ(G)<1 be the spectral radius of G. Then
  E[τ_p(X_0,X_n)] ≤ ρ(G)^n for every 0≤p≤p_{2→2}."

The number 6.4 was checked against the counter. Theorems, propositions and
conjectures share one counter within sections. Section 6 opens at line 1659
with Conjectures 6.1 and 6.2, then Propositions 6.3 and 6.4.

Unimodularity is used in the sense recorded on
`fpbs-hyperbolic-and-nonunimodular-nonuniqueness-citation` from
arXiv:1711.02590: `H <= Aut(G)` is unimodular if `|Stab_v u| = |Stab_u v|`
for all `u,v` in one orbit, where `Stab_x y` is the orbit of `y` under the
stabilizer of `x`.

### 5.2 The graphs

**(a) Regular trees.** For `k>=3`,
`T_k = Cay((Z/2)^(*k), {a_1,...,a_k})`. It is nonamenable and 0-hyperbolic,
so `thm:pell2` gives `p_c<p_(2->2)`. Corollary 4.2 then gives all four kernels,
with a bounded count. `T_k` is a cactus, so PB there was already covered by
`fpbs-cactus-finite-ball-pivotal-budget`.

**(b) Hyperbolic groups.** Let `Gamma` be a nonelementary hyperbolic group and
`S` any finite symmetric generating set. `Cay(Gamma,S)` is connected, locally
finite, transitive and Gromov hyperbolic. It is nonamenable because `Gamma`
contains a free subgroup of rank 2. So `thm:pell2` and Corollary 4.2 apply.

Consider a closed surface group of genus `g>=2` with its standard
presentation. Its Cayley graph is the 1-skeleton of the `{4g,4g}` tiling of
the hyperbolic plane. Every edge borders two distinct tiles, so it lies on two
distinct cycles, and that graph is not a cactus.

**(c) Nonunimodular automorphism subgroups.** Let `k>=3`, `m>=1`,
`Gamma = (Z/2)^(*k) x Z^m` and `S = {a_1,...,a_k} u {+-e_1,...,+-e_m}`.
Then `Cay(Gamma,S)` is the Cartesian product `T_k □ Z^m`.

Fix an end `xi` of `T_k`. Let `H = Aut_xi(T_k) x Z^m` act by
`(x,z) -> (gx, z+t)`.

* `H` is transitive, since `Aut_xi(T_k)` is vertex-transitive on `T_k`.
* `H` is closed in `Aut(G)`: along a pointwise convergent sequence `(g_i,t_i)`,
  `t_i` is eventually constant and `g_i` converges in the closed subgroup
  `Aut_xi(T_k)`.
* `H` is nonunimodular. Let `y` be the neighbour of `x` toward `xi`. The
  stabilizer of `(x,z)` in `H` is `Aut_xi(T_k)_x x {0}`. It fixes the ray from
  `x` to `xi`, and hence fixes `(y,z)`, so `|Stab_(x,z) (y,z)| = 1`. The
  stabilizer of `(y,z)` permutes the `k-1` neighbours of `y` away from `xi`
  transitively, so `|Stab_(y,z) (x,z)| = k-1`.

So `thm:nonunimodular` gives `p_c<p_(2->2)`, and Corollary 4.2 applies. For
`m>=1` the graph is neither hyperbolic nor a cactus:

* it contains an isometric square grid: a geodesic line of `T_k` times the
  `e_1` axis;
* each `e_1` edge lies on at least `k>=3` distinct 4-cycles.

The corresponding `p_c<p_u` statement is recorded on
`fpbs-hyperbolic-and-nonunimodular-nonuniqueness`, from arXiv:1711.02590.

### 5.3 Verdict

On all three families Corollary 4.2 gives PB with a bounded count, together
with IS, NC and RATE. No kernel fails on a graph where `p_c<p_u` is known, so
no obstruction is landed.

The kernels are statements about Cayley graphs. Nothing is claimed for
non-Cayley transitive graphs such as the grandparent graph.

*Remark (transitive graphs; not recorded in Cairn).* Step (b) of Theorem 4.1
used `(F*G)(e)=(G*F)(e)`, which needs the group. On a transitive graph with
symmetric transition matrix `P` and bounded `T_p`, a cruder bound still holds:

    W_n = <delta_o, T_p A T_p P^n delta_o> <= d ||T_p||^2 P^(2n)(o,o)^(1/2).

For the lazy walk this gives
`E[N|E] <= p d ||T_p||^2 P^(2n)(o,o)^(1/2) / P^n(o,o) = exp(o(n))`. That is
enough for formal analogues of RATE, IS and NC, but not for a count of order
`n`.

## 6. The estimate that fails in general

### 6.1 What the method needs

Use the lazy walk. By Theorem 4.1(a) and `a_(n,R) >= mu^n(e)`,

    E_p[N_(n,R) | E_(n,R)] <= p W_n(p) / mu^n(e)    for all R>=n.

So the method of Section 4 proves the kernels on `G` as soon as, for some
`p0>c`:

* (PB) `sup_(c<=p<=p0) W_n(p) <= C n mu^n(e)` for all `n>=1`; or
* (RATE) `sup_(c<=p<=p0) W_n(p) <= exp(alpha n) mu^n(e)` for all large `n`,
  with `alpha<lambda_0/2`.

A better exponential lower bound for `a_(n,R)` is not available.
`a_n(c) = rho^n exp(o(n))` by Lemma 2.3, and `mu^n(e) = rho^n exp(o(n))`.
Section 4 obtains the estimate from `||T_p||<infinity` via Theorem 4.1(b).

### 6.2 The estimate certifies nonuniqueness

**Proposition 6.1.** Let `G` be a nonamenable Cayley graph and
`p in (0,1)`. If `W_n(p)<infinity` for some `n>=1`, then `G[p]` does not have
a unique infinite cluster almost surely.

*Proof.* Fix `x` with `mu^n(x)>0` and `s in S`. Then

    W_n(p) >= mu^n(x) sum_(u in Gamma) tau_p(u) tau_p((us)^(-1)x).

If `G[p]` has a unique infinite cluster, positive association gives
`tau_p(y,z) >= P_p(y<->infinity) P_p(z<->infinity) = theta(p)^2 > 0` for all
`y,z`. So every term is at least `theta(p)^4`, and the sum over the infinite
group diverges. QED

Now fix `p0>c`. If either sufficient estimate of 6.1 holds, then
`W_n(p0)<infinity`. Since `p0>p_c`, `G[p0]` has an infinite cluster, and by
Proposition 6.1 it is not unique. That is a nonuniqueness parameter, which is
already the conclusion of `fpbs-benjamini-schramm-universal` for `G`.

Conversely, suppose `G` has no nonuniqueness parameter. Then for every
`p in (c,1)` the infinite cluster is unique, so `W_n(p)=infinity` for every
`n`, and neither estimate holds for any `p0>c`. The estimate is therefore a
certificate of nonuniqueness. It cannot be used to derive it: a proof of the
estimate would already be a proof of the conclusion, with Russo's formula, the
kernels and the spike theorem playing no role.

### 6.3 Where the loss occurs

Under uniqueness the kernels themselves are finite: `N_(n,R)` is at most the
number of edges of `B_R`. The infinite quantity comes from step (a) of
Theorem 4.1, which makes two replacements:

* the constrained event "`f` is pivotal inside `B_R`" becomes an unconstrained
  BK product;
* the finite-volume connection probabilities become full-space `tau_p`, and
  the pivot position `u` is summed over all of `Gamma`.

Keeping the ball gives a finite bound:

    E_p[N_(n,R); E_(n,R)]
      <= p sum_x mu^n(x) sum_(u, us in B_R) tau_p^(B_R)(e,u) tau_p^(B_R)(us,x)
       =: p W_(n,R)(p).

But `W_(n,R)` increases to `W_n` as `R` grows, by monotone convergence. So at
every uniqueness parameter `sup_(R>=n) W_(n,R)(p) = infinity`. A universal
proof along these lines must keep `R` and control the pivotal event in a way
that is uniform over `R>=n`. This is the same uniformity that the supremum
over radii in `fpbs-universal-subcritical-pivotal-growth-rate` demands. No
such control is proved here.

### 6.4 The class, stated exactly

Let `C_2` be the class of nonamenable Cayley graphs with `p_c<p_(2->2)`.

* **Proved.** All four kernels hold on `C_2`, and PB holds there with a
  bounded count (Corollary 4.2). `C_2` contains the Cayley graphs of
  nonelementary hyperbolic groups and Cayley graphs such as `T_k x Z^m` whose
  automorphism group has a quasi-transitive nonunimodular subgroup
  (Section 5). Most of these are not cacti, and before this note cacti were the
  only class with a verified kernel.
* **Not new for BS.** Every graph in `C_2` already has `p_c<p_u` [H]. This
  note gives no new case of the conjecture.
* **What fails in general.** The Section 6.1 estimates on `W_n(p)` at
  `p>p_c`. By 6.2 they are infinite at every uniqueness parameter.
* **Not attempted.** Whether every nonamenable Cayley graph lies in `C_2` is
  Hutchcroft's question `p_c<p_(2->2)`. That belongs to the L2 operator lane
  and is used here only as a hypothesis.

## 7. Caveats

* **Walks.** The kernels on the tip use different walks:
  * PB names none;
  * IS uses the simple walk;
  * NC and RATE use the lazy walk.

  Every positive result here is proved for both walks. The ordering uses the
  walk transfer of Lemma 2.2 and the lazy reading of PB. The lazy reading is
  the weaker one, so it is safe.
* **Ordering.** Section 3 proves the implications PB ⟹ IS ⟹ NC and PB ⟹ RATE.
  It does not prove that any of them is strict. It does not prove any
  implication between IS or NC and RATE, and it does not prove that none
  exists.
* **Method.** Theorem 4.1 is an elementary BK diagram bound with a
  Cauchy–Schwarz split at the connectivity operator. No priority is claimed
  for the inequality. What this note adds is its consequence for the kernels
  as the archive states them.
* **No new case of the conjecture.** Every graph in the class `C_2` of Section
  6.4 already has `p_c<p_u`, because `p_(2->2)<=p_u` [H, line 301].
* **Tools not used.** Several tools named in the directive are not used:
  * BLPS mass transport; on Cayley graphs, cyclicity of convolution replaces
    it;
  * Hutchcroft's slightly supercritical estimates;
  * Duminil-Copin–Tassion;
  * Aizenman–Kesten–Newman.

  The Hermon–Hutchcroft tail enters only through the separately landed node
  `fpbs-global-pivotal-tail-at-uniqueness`. That node gives exponential tails
  for *global* pivotal counts at a fixed uniqueness parameter. It is uniform
  neither as `p` decreases to `p_c` nor over radii, so it does not control the
  finite-ball supremum in RATE. Section 6.3 locates the loss at the same point.
* **Status.** The proofs are written, not formalized. No computation was run.
  The transitive-graph remark in 5.3 is not recorded in Cairn.

## 8. Cairn nodes

Landed together with this note. Every id was checked against the tip.

* `fpbs-l2-gap-gives-bounded-pivotal-counts`, with `-proof`
  (`requires: []`): Theorem 4.1.
* `fpbs-l2-gap-cayley-graphs-satisfy-pivotal-kernels`, with `-proof`, which
  requires the previous claim: Corollary 4.2.
* `fpbs-hyperbolic-nonunimodular-critical-l2-gap`, with `-citation`
  (`requires: []`): [H] `thm:pell2` and `thm:nonunimodular` at `q=2`.
* `fpbs-pivotal-kernels-hold-on-known-gap-test-graphs`, with `-proof`, which
  requires the second and third claims: Section 5.
* Three conditional routes recording Section 3; the kernels stay OPEN:
  * `fpbs-integrated-sensitivity-from-pivotal-budget` (PB ⟹ IS);
  * `fpbs-nonconcentration-from-integrated-sensitivity` (IS ⟹ NC);
  * `fpbs-subcritical-growth-rate-from-pivotal-budget` (PB ⟹ RATE).
* On all four kernel nodes, an Attempts bullet recording where the method of
  Section 4 dies (Section 6).
* On `fpbs-pivotal-nonconcentration-universal`, a corrected `distinct_from`
  rationale: no strictness is proved.

No obstruction is landed (Section 5.3).

## 9. Sources

* [H] Tom Hutchcroft, *Percolation on hyperbolic graphs*, arXiv:1804.10191.
  Read from its TeX source. The quoted statements begin on lines 298, 301,
  305 (`thm:pell2`), 552 (`thm:nonunimodular`) and 1722 (Proposition 6.4,
  `prop:nonuniquenessatpell2`).
* [HH] Jonathan Hermon and Tom Hutchcroft, arXiv:1904.10448, Theorem 1.1 (TeX
  source lines 393–401). Used here only through
  `fpbs-supercritical-finite-susceptibility` and
  `fpbs-global-pivotal-tail-at-uniqueness`.
* The `p_c<p_u` theorem of arXiv:1711.02590 enters only through
  `fpbs-hyperbolic-and-nonunimodular-nonuniqueness-citation`. It was not
  re-read for this note.
* Archive notes:
  * `research/artifacts/fpbs/exploration.md`: (2.2) and Proposition 3;
  * `research/artifacts/fpbs/exploration-pivotal-projections.md`: Section 6;
  * `research/artifacts/fpbs/spectral-spike.md`: Section 6 and Corollary 6.2.
