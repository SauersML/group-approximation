---
rg: 2
id: fpbs-walk-rate-holes-fail-on-unimodular-random-graphs-proof
kind: route
title: Prove the annealed Schramm lemma, a deterministic Cheeger bound and the uniqueness floor on the stretched Angel--Hutchcroft graph
target: fpbs-walk-rate-holes-fail-on-unimodular-random-graphs
requires:
  - fpbs-bounded-query-connection-strong-converse
---

Notation as in the target. A *graph functional* is a Borel function of rooted or
doubly rooted graphs, invariant under rooted isomorphism. Quenched percolation and
walk expectations of events on a fixed realization are graph functionals.
Unimodularity of `mu` is the mass-transport principle (MTP): for every Borel
`f(G,x,y) >= 0`,

    E_mu sum_y f(G,o,y) = E_mu sum_x f(G,x,o).

All graphs below are simple. `deg` is the degree, `pi(K) = vol(K) = sum_{x in K} deg(x)`,
and `P = (I + Q)/2`, where `Q` is the simple random walk. Both are self-adjoint
on `l2(G,deg)`, and `deg(x)P^n(x,y) = deg(y)P^n(y,x)`.

## 1. Cheeger implies a uniform gap (Theorem 1.1)

Let `f` be finitely supported and write `E(f) = sum_{edges xy} (f(x)-f(y))^2`,
which equals `<f,(I-Q)f>_deg`. Put `g = f^2`. By the co-area formula,

    sum_{xy} |g(x)-g(y)| = int_0^inf |d_E {g>t}| dt >= Phi int_0^inf vol{g>t} dt
                         = Phi ||f||^2.

By Cauchy--Schwarz the left side is at most
`sqrt(E(f)) sqrt(sum_{xy}(f(x)+f(y))^2) = sqrt(E(f)(2||f||^2 - E(f)))`. With
`t = E(f)/||f||^2` this gives `Phi^2 <= t(2-t)`, that is `(1-t)^2 <= 1 - Phi^2`.
So `<f,Qf>/||f||^2 = 1-t <= sqrt(1-Phi^2)`. Since `<f,Qf> <= <|f|,Q|f|>`, the spectrum
of `Q` lies in `[-1, sqrt(1-Phi^2)]`. So the spectrum of `P` lies in
`[0, rho_bar]` and `||P^n|| <= rho_bar^n`. QED.

## 2. Annealed Schramm lemma (Theorem 1.2)

First let `p < p_c(H)`. Almost surely every cluster `K(x)` of the realization is
finite. Define

    f(G,x,y) = E_omega[ deg(x) sum_{z in K(x)} P^n(x,z) * deg(y) 1{y in K(x)} / pi(K(x)) ].

The out-mass at `o` is `deg(o) P_p(o <-> X_n)`, with the walk independent of `omega`.
The in-mass at `y` is

    E_omega[ deg(y) <1_K, P^n 1_K>_deg / pi(K) ],   K = K(y),

which is at most `deg(y) rho_bar^n` by Section 1. The MTP gives
`E_mu[deg(o) P_p(o<->X_n)] <= rho_bar^n E_mu deg(o)`, that is
`a_n(p) <= rho_bar^n`.

Now take `p = p_c`. For fixed `G`, `o` and walk path, `{o <-> X_n}` is the
increasing union of the cylinder events `A_L = {o <-> X_n by a path of length <= L}`.
Each `P_p(A_L)` is a polynomial in `p`. Therefore

    P_{p_c}(o<->X_n) = sup_L sup_{p<p_c} P_p(A_L) = sup_{p<p_c} P_p(o<->X_n),

and monotone convergence gives `a_n(p_c) <= rho_bar^n`. QED.

## 3. Uniqueness floor (Theorem 1.3)

**Stationarity and self-adjointness.** For a graph functional `h(G,x)`, put
`(P^n h)(G,x) = sum_z P^n(x,z) h(G,z)`. Apply the MTP to
`f(G,x,y) = deg(x) P^n(x,y) h1(G,x) h2(G,y)` and use
`deg(x)P^n(x,y) = deg(y)P^n(y,x)`. This gives `<h1, P^n h2> = <P^n h1, h2>` in
`L2(mu_hat)`. Taking `h1 = 1` gives stationarity, `E_mu_hat P^n h2 = E_mu_hat h2`.
Jensen's inequality and stationarity give `||P h|| <= ||h||`. The same holds for `Q`.

**Positivity above the mean.** Write `h = m + h0`, where `m = E_mu_hat h` and
`E h0 = 0`. Then `<1, P h0> = <P1, h0> = 0`. Also
`<h0, P h0> = (||h0||^2 + <h0,Q h0>)/2 >= 0`. So `<h, P h> >= m^2`. For `n = 2k`,
`<h, P^n h> = ||P^k h||^2 >= (E P^k h)^2 = m^2`. For `n = 2k+1`, apply the previous
bound to `P^k h`, whose mean is `m`.

**The floor.** Let `theta(G,x) = P_p(x in an infinite cluster)` and suppose a.s.
there is exactly one infinite cluster `I`. For fixed `G`, `o` and walk position `z`,
`{o in I} ∩ {z in I}` is contained in `{o<->z}`. Harris--FKG gives
`P_p(o<->z) >= theta(G,o) theta(G,z)`. Averaging over the walk and over
`mu_hat` gives `a_n(p) >= <theta, P^n theta> >= (E_mu_hat theta)^2`.

**Positivity of the mean.** Suppose `E_mu theta(G,o) = 0`. On `{I != empty}`, let
`N(x)` be the finite nonempty set of vertices of `I` closest to `x`. Put
`f(G,x,y) = E_omega[1{I != empty} 1{y in N(x)} / |N(x)|]`.

* The out-mass is `P_omega(I != empty) = 1`.
* The in-mass at `o` vanishes unless `o in I`, which has annealed probability `0`.
  So its expectation is `0`.

The MTP then gives `1 = 0`, a contradiction. So `E_mu_hat theta >= E_mu theta / D > 0`.
QED.

## 4. Annealed strong converse (Theorem 1.4)

Proposition 1 of `research/artifacts/fpbs/query-strong-converse.md` is stated for
any infinite graph and an independent seed. Apply it on each realization with
`a_G = P_{c,G}(o<->X_n)`:

    P_{q,G}(E_m) <= a_G^((alpha-1)/alpha) exp(m (alpha-1) D_alpha(q||c)/alpha).

Average over `mu_hat`. Since `x -> x^((alpha-1)/alpha)` is concave, Jensen and
Section 2 give `E_mu_hat P_q(E_m) <= rho_bar^(n(alpha-1)/alpha)
exp(m(alpha-1)D_alpha/alpha)`. The choice of `alpha` and `eta` in the proof of
Theorem 2 there applies verbatim, with `lambda = -log rho_bar`. QED.

## 5. The Angel--Hutchcroft graph (Theorem 2)

**Imports.** Angel and Hutchcroft, *Counterexamples for percolation on unimodular
random graphs*, arXiv:1710.03003v1, quoted verbatim.

* Theorem 1.4: "There exists a unimodular random rooted graph (G, rho) such that G
  has bounded degrees, is nonamenable, and has p_c(G) = p_u(G) for Bernoulli bond
  percolation almost surely."
* Section 4.2: "Finally, given a constant M >= 1, we define the graph H~(M) by
  replacing each of the S-edges of H with a path of length M. It follows by
  replacement that H~(M) can be rooted in such a way that it is a unimodular random
  rooted graph."
* Proposition 4.2: "The random graph H~(M) described has bounded degrees and is
  nonamenable. If M is sufficiently large then p_c(H~) = p_u(H~) = q."
* In its proof: "given any finite set of vertices K in H, we can write K = U_{i in I}
  K_i where K_i = K ∩ V_i ... we have that |d_E K| >= sum_{i in I} |K_i| = |K|".
* Proof of Lemma 4.3: "Thus, for every p > q, every type-1 copy of G in H~ contains
  a unique infinite open cluster almost surely. It is easy to deduce using insertion
  tolerance and the mass-transport principle that these clusters must all be
  connected to each other by open edges in H~. Finally, indistinguishability implies
  that there cannot be any other infinite open cluster in H~".
* Same proof: "It is easily verified that G is invariantly amenable".

**Degree bound.** The degrees are deterministic. A vertex `(v1,v2,W)` has at most
`4` S-edges. Its G-edges pair a neighbour of `v1` in `G` with a neighbour of `W` in
the tree `D`, which has fold at most `4`. `G` has bounded degrees ("immediate from
the assumption that r and m have bounded increments"). Let `D` be the resulting
deterministic bound. Path interiors have degree `2`.

**Deterministic Cheeger bound for H~.** Let `K` be a finite vertex set of `H~` and
`A = K ∩ V(H)`. Call an S-path *full* if all `M+1` of its vertices lie in `K`, and
*partial* if it meets `K` but is not full. Every partial path contains a boundary
edge of `K`, and distinct paths have disjoint edges.

* Each G-edge of `d_E^H A` is a boundary edge of `K` in `H~`.
* Each S-edge of `d_E^H A` belongs to a partial path.
* Hence `|d_E K| >= |d_E^H A| >= |A|`, by the imported bound.
* Also `|d_E K| >= #partial`.
* A full path has both endpoints in `A`, so `#full <= D|A|/2`.

Counting path interiors,

    |K| <= |A| + (M-1)(#full + #partial) <= (1 + (M-1)(D/2 + 1)) |d_E K|
        <= M (D+1) |d_E K|.

Since `vol(K) <= D|K|`, every realization has `Phi >= Phi_0 = 1/(D M (D+1))`.

**Conclusion.** By Proposition 4.2, `p_c = q` a.s. For `p < q` there is a.s. no
infinite cluster, so Section 2 gives `lambda_hat(q) <= rho_bar`. For `p > q` the
quoted proof of Lemma 4.3 gives a unique infinite cluster, so Section 3 gives
`a_n(p) >= m(p)^2 > 0` and `lambda_hat(p) = 1`. Summing over `n`,
`E A(q) <= sum rho_bar^n <= 1/(1-rho_bar)` and `E A(p) = infinity` for `p > q`.
QED.

## 6. The Corollary

* **(IS) and green-visit.** These are immediate from Section 5.
* **Uniform pivotal budget.** Suppose that for deterministic `C` and `p0 > q`, and
  for `mu_hat`-a.e. root, `E_p[N_(n,R) | E_(n,R)] <= Cn` for all `p in [q,p0]`,
  `n >= 1` and `R >= n`.
  - Russo's formula on the fixed realization, averaged over the independent walk,
    gives `d/dp log a^G_(n,R)(p) = E_p[N|E]/p`.
  - Integrating gives `a^G_(n,R)(p) <= a^G_(n,R)(q) (p/q)^(Cn)`.
  - Let `R -> infinity` (monotone) and average: `a_n(p) <= (rho_bar (p/q)^C)^n`.
  - Choose `p in (q,p0]` with `rho_bar (p/q)^C < 1`. This contradicts `a_n(p) >= m(p)^2 > 0`.
* **Section 5 construction.** On `H~` the premise "collapse" is true at every
  `q' > q`, and Theorem 1.4 still forbids linear-budget certificates with
  subexponential annealed success probability.

The class-kill statement then follows as written in the target. The inputs 1--4
listed there hold on every realization of `H~` or, for the MTP items, under `mu`
(Aldous--Lyons generalizations, as quoted in the proof of Lemma 4.3). Any
conclusion derived from them in root-averaged form holds on `H~`, and the four
holes do not.
