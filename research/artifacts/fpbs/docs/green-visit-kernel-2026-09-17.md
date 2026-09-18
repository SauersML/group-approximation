# The Green-summed visit kernel below the pivotal kernels

Agent swarm-0917-w4-bs-pivotal, wave swarm-0917, 2026-09-17. Target cone:
`fpbs-pivotal-budget-universal` toward `fpbs-benjamini-schramm-universal`.
No computation is used. All proofs are complete below.

## Status and scope

The tip has four pivotal kernels, PB, IS, NC and RATE
(`pivotal-kernel-ordering-2026-09-12.md`, Section 1). Each asks for control of
the walk-averaged connection probability `a_n(p)` at every length `n`. This
note sums over `n` first. That gives two new kernels:

* **(VIS)** some `p>p_c` has `A(p) := sum_(n>=0) a_n(p) < infinity`. By
  Tonelli, `A(p)` is the expected number of times an independent walk started
  at `e` visits the cluster of `e`.
* **(GB)** the Green-summed Russo derivative is bounded: there are `C` and
  `p0>p_c` with `E^(tilt)_(p,R)[N] <= C` for all `R` and `p in [p_c,p0]`
  (definition in Section 2).

Proved here (Theorem 3.1):

    PB => GB => VIS => BS,      (p_c < p_(2->2)) => GB,
    NC => VIS,                  (tau_p in l2 for some p>p_c) => VIS.

So VIS is implied by every quantitative hypothesis on the tip that is known to
give BS, and it gives BS by a one-line argument. Not proved: any converse, and
whether VIS holds on every nonamenable Cayley graph. That is the new open node
`fpbs-green-visit-criterion-universal`.

## 1. Setup

Notation is that of `pivotal-kernel-ordering-2026-09-12.md`, Section 1:
`G=Cay(Gamma,S)` is nonamenable, `d=|S|`, `c=p_c(G)`, `tau_p(x)=P_p(e<->x)`,
`T_p` is right convolution by `tau_p` on `l2(Gamma)`, and `A=1_S`. The step law
`mu` is the simple walk `mu_S` or the lazy walk `mu_L=(delta_e+mu_S)/2`, with
`l2` norms `rho_S<1` (Kesten) and `rho_L=(1+rho_S)/2<1`. For `R>=0` and `n>=0`:

* `E_(n,R)` is the event that `e` connects to `X_n` inside the ball `B_R`;
* `a_(n,R)(p)=P_p(E_(n,R))` and `a_n(p)=lim_R a_(n,R)(p)=E tau_p(X_n)`;
* `N_(n,R)` is the number of open edges pivotal for `E_(n,R)`.

Note `a_(0,R)=1` and `N_(0,R)=0`. Finite-volume Russo on the finite graph
`B_R`, averaged over the independent walk, gives for every `n` and `R`

    d/dp a_(n,R)(p) = E_p[N_(n,R); E_(n,R)] / p.                 (1.1)

(This is (1.1) of the ordering note multiplied by `a_(n,R)`; it holds for all
`n`, since both sides vanish on walk paths whose endpoint lies outside `B_R`.)

**Walk transfer for sums.** `X^L_n = X^S_(K_n)` with `K_n ~ Bin(n,1/2)`
independent of everything, and the event depends only on the endpoint. Since
`sum_(n>=0) P(K_n=k) = 2` for every `k>=0`,

    A_L(p) = sum_n E a^S_(K_n)(p) = 2 A_S(p).                    (1.2)

So VIS does not depend on the walk.

## 2. The two kernels

Let `g = sum_(n>=0) mu^n` be the Green function of the walk. For `R>=0` put

    A_R(p) = sum_(n=0)^R a_(n,R)(p),
    E^(tilt)_(p,R)[N] = sum_(n=1)^R E_p[N_(n,R); E_(n,R)] / A_R(p).

The truncation `n<=R` matches the range `R>=n` in PB. Each `a_(n,R)` is a
polynomial in `p`, `A_R>=a_(0,R)=1`, and (1.1) gives

    d/dp log A_R(p) = E^(tilt)_(p,R)[N] / p.                     (2.1)

Here `E^(tilt)` is the pivotal count of the connection from `e` to a random
endpoint in the ball, where the endpoint is weighted by its truncated Green
mass inside the cluster of `e`.

As `R` grows, `a_(n,R)` increases and more terms appear. By monotone
convergence `A_R(p)` increases to

    A(p) = sum_n a_n(p) = sum_x g(x) tau_p(x) = E #{ n : X_n in C(e) }.   (2.2)

* **(VIS)** there is `p>c` with `A(p)<infinity`.
* **(GB)** there are `C<infinity` and `p0>c` with `E^(tilt)_(p,R)[N] <= C`
  for all `R>=0` and all `p in [c,p0]`.

Both are read with a fixed walk. By (1.2), VIS does not depend on which walk.
GB is proved below for whichever walk the hypothesis is read with.

**Critical value.** For either walk,

    A(c) <= 1/(1-rho).                                          (2.3)

For the simple walk, `fpbs-critical-walk-correlation` gives
`a^S_n(c) <= rho_S^n`. For the lazy walk,
`a^L_n(c) = E a^S_(K_n)(c) <= E rho_S^(K_n) = rho_L^n`.

**A bound on the Green function.** `mu` is symmetric, so
`||mu^n||_2^2 = mu^(2n)(e) = <delta_e, P^(2n) delta_e> <= rho^(2n)`. Hence

    ||g||_2 <= sum_n ||mu^n||_2 <= 1/(1-rho).                     (2.4)

## 3. The ordering

**Theorem 3.1.** On every nonamenable Cayley graph, for either walk:

(a) If `A(p)<infinity`, there is no unique infinite cluster at any `p'<=p`.
    In particular VIS implies `p_c<p_u`.
(b) GB on `[c,p0]` implies `A(p) <= (p/c)^C/(1-rho)` for all `p in [c,p0]`.
    So GB implies VIS.
(c) PB, read with the lazy walk (the weaker reading; ordering note Section 1),
    implies GB for the lazy walk.
(d) If `||T_(p0)||_(2->2)<infinity` for some `p0>c`, then GB holds on
    `[c,p0]` with `C = d ||T_(p0)||^2/(1-rho)`.
(e) NC implies VIS.
(f) If `tau_p in l2(Gamma)`, then `A(p) <= ||tau_p||_2/(1-rho)`.

*Proof of (a).* `A` is nondecreasing in `p`, since each `a_n` is. Suppose
there is a unique infinite cluster at some `p'<=p`. Then `theta(p')>0`. By
Harris–FKG, `P(e<->infinity, x<->infinity) >= theta(p')^2`, and by uniqueness
this event implies `e<->x`. So `tau_(p')(x)>=theta(p')^2` for every `x`, hence
`a_n(p')>=theta(p')^2` for every `n`, and `A(p)>=A(p')=infinity`, a
contradiction. If also `p>c`, then no parameter in `[0,p]` has a unique
infinite cluster, so `p_u>=p>c`. QED.

*Proof of (b).* Integrating (2.1) over `[c,p]` gives
`log A_R(p) - log A_R(c) <= C log(p/c)`. By monotonicity and (2.3),
`A_R(c) <= A(c) <= 1/(1-rho)`. Let `R->infinity` and use (2.2). QED.

*Proof of (c).* PB gives `C,p0` with `E_p[N_(n,R)|E_(n,R)] <= Cn` for
`1<=n<=R` and `p in [c,p0]`. Integrate (1.1) divided by `a_(n,R)`, then use
`a_(n,R)(c) <= a^L_n(c) <= rho_L^n`:
`a_(n,R)(p) <= (rho_L (p/c)^C)^n`. Since `rho_L<1` we may fix `p1` with
`c < p1 < min(p0, c rho_L^(-1/C))`; set `r = rho_L (p1/c)^C < 1`. For
`p in [c,p1]`,

    sum_(n=1)^R E_p[N_(n,R);E_(n,R)] <= C sum_(n>=1) n a_(n,R)(p) <= C r/(1-r)^2,

and `A_R(p)>=1`. So GB holds on `[c,p1]` with constant `C r/(1-r)^2`. QED.

*Proof of (d).* Fix `p in [c,p0]` and `1<=n<=R`. On `E_(n,R)` with endpoint
`x`, take a simple open path from `e` to `x` in `B_R`. It crosses each open
pivotal edge `f={u,us}` exactly once, say from `u` to `us`. The pieces before
and after are disjoint from each other and from `f`. So the event
`{e<->u in B_R} o {f open} o {us<->x in B_R}` occurs. By BK and monotonicity
in the volume, its probability is at most `tau_p(u) p tau_p((us)^(-1)x)`.
Summing over directed pairs `(u,s)`, which covers both orientations, and
averaging over the walk gives

    E_p[N_(n,R);E_(n,R)] <= p W_n,   W_n = sum_x mu^n(x) (tau_p*A*tau_p)(x).

This is step 1 of `fpbs-l2-gap-gives-bounded-pivotal-counts-proof`. By
Tonelli and Cauchy–Schwarz,

    sum_(n=1)^R W_n <= <g, tau_p*(A*tau_p)> <= ||g||_2 ||tau_p*(A*tau_p)||_2.

Write `f^v(x)=f(x^(-1))`. Then `(f*h)^v = h^v*f^v` and `tau_p^v=tau_p`, so
left convolution by `tau_p` has norm `||T_p||`. Also
`||A*tau_p||_2 <= d ||tau_p||_2 = d ||T_p delta_e||_2 <= d ||T_p||`. A
nonnegative kernel's `l2` norm is attained on nonnegative functions, so it is
nondecreasing in `p`. With (2.4),

    sum_(n=1)^R W_n <= d ||T_(p0)||^2/(1-rho).

Since `p<=1` and `A_R>=1`, GB follows. QED.

*Proof of (e).* NC gives some `eps>0` with `B(eps) < -log rho_L`. By (1.1),
`M_(n,R)(c+eps) = n^(-1) log(a_(n,R)(c+eps)/a_(n,R)(c))`. As `R->infinity`
this tends to `n^(-1) log(a_n(c+eps)/a_n(c))`, because both probabilities
increase to positive limits. Using `a^L_n(c) <= rho_L^n`,

    limsup_n n^(-1) log a^L_n(c+eps) <= log rho_L + B(eps) < 0.

So `a^L_n(c+eps)` decays exponentially and `A_L(c+eps)<infinity`. QED.

*Proof of (f).* Apply Cauchy–Schwarz to (2.2), then use (2.4). QED.

**Corollary 3.2.** Let `p_A = sup{p : A(p)<infinity}`. Then

    c <= max( p_(2->2), sup{p : lambda(p)<1} ) <= p_A <= p_u,

and VIS is exactly the statement `p_A>c`.
* The first inequality uses `c <= p_(2->2)` [H, quoted in ordering note 5.1].
* The second uses (f) for `p<p_(2->2)`, where `tau_p = T_p delta_e in l2`. It
  also uses `a_n <= lambda(p)^n` (ordering note Lemma 2.1).
* The third is (a).

## 4. What this changes, and where it stops

1. **New weakest target.** Every quantitative hypothesis on the tip that is
   known to give BS by a Russo or operator argument (PB, IS through NC, NC,
   and the l2 gap) implies VIS. VIS gives BS in one line. RATE is the only
   kernel not placed: RATE ⇒ VIS is not proved. So a universal proof of
   VIS suffices, and a counterexample to VIS on one nonamenable Cayley graph
   refutes all of PB, NC, IS and `p_c<p_(2->2)` there at once. That would be
   a sharper obstruction than any single-kernel counterexample.
2. **What VIS asks for.** It asks only that the independent walk spend finite
   expected time in the cluster of its starting point at one parameter above
   `p_c`. Unlike NC and IS, it tolerates `lambda(p)=1`, that is,
   subexponential but summable decay of `a_n`. Unlike PB and GB, it has no
   derivative content.
3. **Where every kernel in this family stops.** `A(p)=infinity` at every
   uniqueness parameter, by (a). So VIS, like the full-space bubble of
   ordering note Section 6, certifies nonuniqueness and cannot be derived from
   it without new input. What is new is the size of the certificate. Near
   criticality it can be checked on `sum_x g(x) tau_p(x)`, which is linear in
   `tau_p` and weighted by the `l2` function `g`. The bubble in Section 6 is
   quadratic in `tau_p`.
4. **Not proved.** Any converse. Whether `p_A = p_u` on the known examples.
   Whether `A(p_A)<infinity`. RATE ⇒ VIS.
