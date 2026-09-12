# The one-radius sphere fibre condition is critical L2 boundedness

Lane `bs-sphere-operator-one-ended`, 2026-09-12. Setting and notation are those
of `research/artifacts/fpbs/docs/sphere-cut-fibre-bootstrap.md`: `Gamma` finitely
generated, `S` a finite symmetric generating set, `X = Cay(Gamma,S)`, `H` normal
in `Gamma`, `Q = Gamma/H` with word length `|.|` from `pi(S)`, fibres
`Gamma_q = pi^(-1)(q)`, and for `f >= 0` on `Q`

    sigma_p(q) = sum_{x in Gamma_q} tau_p(o,x),    sigma_{p,R} = sigma_p 1_{S_Q(R)},
    C_{p,r}    = sigma_p 1_{|.| >= r},              N(f) = ||lambda_Q(f)||_{2->2} in [0,infinity],
    (f*g)(q)   = sum_{q'} f(q') g(q'^(-1) q).

The lane's task was the open claim `fpbs-critical-sphere-fibre-operator-below-one`
over one-ended hyperbolic quotients (surface groups times `Z`, Seifert-fibred
groups). This note does not prove that claim. It proves the claim is equivalent,
over every quotient, to boundedness of the critical fibre operator. For amenable
kernels that is Hutchcroft's L2 boundedness conjecture on the same Cayley graph.
The note also shows that the single-kernel inequalities used so far cannot give
the claim, and where the nonunimodular tilting method stops. Nothing here is
refereed or formalized.

## 0. Inputs

* **(F1) Sphere cut.** For every `p`, every `R >= 0` and every `q` with `|q| >= R`,
  `sigma_p(q) <= sum_{q' in S_Q(R)} sigma_p(q') sigma_p(q'^(-1) q)` in `[0,infinity]`.
  Every `q'` in the sum has `|q'^(-1) q| >= |q| - R`. This is Lemma 1.1 of the
  bootstrap artifact (`fpbs-sphere-cut-fibre-tails-decay-exponentially`).
* **(F2) Positive kernels.** For `f, g >= 0`: `N(f*g) <= N(f) N(g)`; if `f <= g`
  entrywise then `N(f) <= N(g)`; and `||f||_inf <= N(f) <= ||f||_1`. The norm is the
  supremum of `<G, f*F>` over nonnegative finitely supported unit vectors `F, G`.
* **(F3) Left limits.** `p -> sigma_p(q)` is nondecreasing and left-continuous
  (bootstrap artifact, Theorem 2.1, step 4). By (F2) and monotone convergence,
  `N(sigma_{p_c} 1_A) = sup_{p<p_c} N(sigma_p 1_A)` for every `A ⊆ Q`.
* **(F4) Fibre comparison.** `||T_p|| <= N(sigma_p)` for every normal `H`, with
  equality when `H` is amenable (`fpbs-fibre-summed-connectivity-operator`). Right
  convolution by the symmetric `sigma_p` is unitarily equivalent to `lambda_Q(sigma_p)`.
* **(F5) Openness of the L2 phase.** Hutchcroft arXiv:1804.10191, Section 2, the
  corollary of Lemma `lem:operatorbound` (cited on main as Corollary 2.6):
  `||T_p|| >= (1-p)/(|S| (p_{2->2} - p))` for `p < p_{2->2}`, so
  `||T_{p_{2->2}}|| = infinity`. Hence `||T_{p_c}|| < infinity` iff `p_c < p_{2->2}`.
* **(F6) Sharpness.** For `p < p_c`, `N(sigma_p) <= chi_p < infinity`.

## 1. The equivalence

**Theorem A.** For every `Gamma`, `S` and normal subgroup `H`, the following
are equivalent on `X`:

* **(a)** `N(sigma_{p_c,R_0}) < 1` for some `R_0 >= 1`;
* **(b)** `N(sigma_{p_c}) < infinity`, that is, the critical fibre operator is
  bounded on `l2(Q)`;
* **(c)** there is `M < infinity` with `N(C_{p_c,r}) <= M e^(-r/M)` for all `r >= 0`.

They imply `p_c(X) < p_{2->2}(X)`. If `H` is amenable, they are equivalent to
`p_c(X) < p_{2->2}(X)`.

*Proof of (a) ⟹ (b).* Put `theta = N(sigma_{p_c,R_0}) < 1`.
1. **Small radii.** Fix `q_0 in S_Q(R_0)`. For each `q` with `|q| < R_0` fix
   `g_q in Gamma` with `pi(g_q) = q^(-1) q_0`, and let `L = max_q |g_q|_S`. Right
   multiplication by `g_q` maps `Gamma_q` onto `Gamma_{q_0}`. Harris–FKG gives
   `tau_p(o, x g_q) >= tau_p(o,x) tau_p(o,g_q) >= p^L tau_p(o,x)`. Summing over
   `x in Gamma_q`, `sigma_p(q) <= p^(-L) sigma_p(q_0)`. Also
   `sigma_p(q_0) <= N(sigma_{p,R_0}) <= theta` by (F2) and monotonicity in `p`.
2. **Large radii.** By (F1) with `R = R_0`, `C_{p,R_0} <= sigma_{p,R_0} * sigma_p`
   entrywise. So `N(C_{p,R_0}) <= theta N(sigma_p)`.
3. **Absorb.** For `p in [p_c/2, p_c)`, since `sigma_p = sigma_p 1_{|.|<R_0} + C_{p,R_0}`,

       N(sigma_p)  <=  ||sigma_p 1_{|.|<R_0}||_1 + N(C_{p,R_0})
                   <=  |B_Q(R_0)| (p_c/2)^(-L) theta + theta N(sigma_p).

   `N(sigma_p)` is finite by (F6), so
   `N(sigma_p) <= (1-theta)^(-1) |B_Q(R_0)| (p_c/2)^(-L) theta`.
4. **Limit.** (F3) passes this bound to `p_c`. QED.

*Proof of (b) ⟹ (c).* This is Hutchcroft's proof of arXiv:1904.05804,
Proposition 2.4, run on fibre sums. It works at any `p` with
`N_p := N(sigma_p) < infinity`.
1. **Averaged cut.** Let `n, m >= 0` and `0 <= r <= m`. By (F1) with `R = r`,
   `C_{p,n+r} <= sigma_{p,r} * C_{p,n}`, because every `q'` in the sum has
   `|q'^(-1) q| >= |q| - r >= n`. Since `C_{p,n+m} <= C_{p,n+r}` and
   `sum_{r=0}^m sigma_{p,r} <= sigma_p`,

       C_{p,n+m}  <=  (m+1)^(-1) sum_{r=0}^{m} sigma_{p,r} * C_{p,n}  <=  (m+1)^(-1) sigma_p * C_{p,n}.

2. **Iterate.** By (F2), `N(C_{p,n+m}) <= N_p N(C_{p,n}) / (m+1)`. Take `m = n` and
   induct from `C_{p,0} = sigma_p`: `N(C_{p,kn}) <= (N_p/(n+1))^k N_p`.
3. **Choose `n`.** `N_p >= sigma_p(1) >= tau_p(o,o) = 1`. Put `n = ceil(e N_p) - 1`,
   so `n >= 2`, `n < e N_p` and `n + 1 >= e N_p`. Then `N(C_{p,kn}) <= e^(-k) N_p`.
   For `r >= 0` put `k = floor(r/n)`. Since `C_{p,r} <= C_{p,kn}`,

       N(C_{p,r})  <=  e^(-floor(r/n)) N_p  <=  e N_p exp(-r/(e N_p)).

   So (c) holds with `M = e N_p`. QED.

*Proof of (c) ⟹ (a).* `sigma_{p_c,r} <= C_{p_c,r}`, so
`N(sigma_{p_c,r}) <= M e^(-r/M) < 1` once `r > M log M`. QED.

*The L2 gap.* By (b) and (F4), `||T_{p_c}|| <= N(sigma_{p_c}) < infinity`, and (F5)
gives `p_c < p_{2->2}`. If `H` is amenable and `p_c < p_{2->2}`, then
`||T_{p_c}|| < infinity` by monotonicity in `p`, and the equality in (F4) gives (b).
QED.

**Remarks.**
* **Pointwise decay.** Under (b), `sigma_{p_c}(q) <= N(C_{p_c,|q|}) <= e N exp(-|q|/(eN))`
  with `N = N(sigma_{p_c})`. For amenable `H` the same bound holds at every
  `p < p_{2->2}` with `N = ||T_p||`. This is the fibre analogue of arXiv:1904.05804,
  Remark 2.3.
* **Amenable quotients.** If `Q` is amenable, `N(sigma_{p_c}) = chi_{p_c} = infinity`,
  so (a) fails on every Cayley graph. This agrees with Corollary 2.2 of the
  bootstrap artifact.
* **No quotient geometry.** Hyperbolicity, rapid decay and one-endedness are not
  used. The argument is the same for free, surface and triangle-group quotients.

## 2. What this says about the hyperbolic-quotient premises

**Corollary B.** Let `H` be amenable and let `Q` have rapid decay with exponent
`D`. On each Cayley graph `X` of `Gamma` the following are equivalent:

* the one-radius condition (a), which is `fpbs-critical-sphere-fibre-operator-below-one` at `X`;
* `W_D(p_c) < infinity`, which is `fpbs-rd-quotient-weighted-critical-fibre-bubble` at `X`;
* `p_c(X) < p_{2->2}(X)`, Hutchcroft's L2 boundedness conjecture
  (arXiv:1904.05804, Conjecture 1.3) at `X`.

They imply the unweighted critical fibre bubble.

*Proof.* The first two are equivalent by
`fpbs-rd-weighted-bubble-iff-sphere-fibre-operator-below-one`, and the first and
third by Theorem A. The bubble is `fpbs-amenable-kernel-l2-gap-forces-fibre-bubble`. QED.

**Consequences.**
* **Groups with an infinite amenable centre or `Z^k` kernel.** This covers surface
  groups times `Z`, Seifert-fibred groups, `hyperbolic x Z^k` and central
  extensions. There the one-radius premise is the L2 boundedness conjecture itself.
  The bootstrap artifact called it "a reformulation of the premise at one radius,
  not a weaker premise". Theorem A shows it is no weaker than critical L2
  boundedness either.
* **The sandwich collapses on one side.** The RD artifact placed the L2 gap between
  the weighted bubble (sufficient) and the unweighted bubble (necessary). For
  amenable kernels over RD quotients, the weighted bubble is equivalent to the gap.
* **Nonamenable kernels,** for example `F_2 x F_2` with `H = F_2`: (a) is
  equivalent to boundedness of the fibre operator. That implies `||T_{p_c}|| < infinity`
  and may be strictly stronger.
* **One-ended quotients are needed.** If `M` is Seifert-fibred over the orbifold
  `S^2(2,3,7)`, then `pi_1(M)` has no nonabelian free quotient. A map onto a free
  group kills the centre, so it factors through the triangle group, whose
  generators are torsion. So free-quotient methods do not replace one-ended
  quotients in Choi–Seo Question 1.6.

## 3. Where the condition is known to hold

**Proposition C.** Let `mubar` be the image in `Q` of the uniform measure on `S`.
It is a symmetric probability measure with spectral radius `rho = N(mubar)`. If
`p |S| rho < 1`, then `N(sigma_p) <= (1 - p |S| rho)^(-1)`. In particular, if
`p_c(X) |S| rho < 1`, then (a)–(c) of Theorem A hold.

*Proof.* A union bound over open paths gives `tau_p(o,x) <= sum_n p^n A^n(o,x)`.
The walks of length `n` from `o` ending in `Gamma_q` number `|S|^n mubar^(*n)(q)`. So
`sigma_p <= sum_n (p|S|)^n mubar^(*n)` entrywise, and
`N(sigma_p) <= sum_n (p|S| rho)^n`, because `lambda_Q(mubar)` is self-adjoint. QED.

This is the walk-counting mechanism behind the perturbative proofs listed in
arXiv:1904.05804, page 4 (small spectral radius, large Cheeger constant). Nothing
forces `p_c |S| rho < 1` on a general generating set.

## 4. The single-kernel inequalities do not imply the condition

About the critical two-point function, the proofs on main use only these facts:
* `tau(o,o) = 1` and `0 <= tau <= 1`;
* symmetry, `tau(o,x^(-1)) = tau(o,x)`;
* Harris–FKG supermultiplicativity;
* the BK sphere cut (F1), at the level of `tau`;
* divergence of `sum_x tau(o,x)`;
* and, as a premise, a finite fibre bubble.

The following kernel has all of these and fails (a) at every radius.

**Proposition D.** Let `Gamma = F_2 x Z` with `S = {(a^(±1),0), (b^(±1),0), (1,±1)}`,
`H = {1} x Z` and `Q = F_2`. Fix `alpha > 0` with `coth(alpha) >= 3`, and put

    f(n) = 2 * 3^(-n/2) / (2+n)   (n >= 0),      tau(o,(q,m)) = f(|q|) e^(-alpha |m|),

with `tau(x,y) = tau(o, x^(-1) y)`. Let `sigma(q) = sum_m tau(o,(q,m))`. Then:
1. `tau(o,o) = 1`, `0 < tau <= 1` and `tau(o,x^(-1)) = tau(o,x)`;
2. `tau(o,xy) >= tau(o,x) tau(o,y)` for all `x, y`;
3. for every `R >= 0` and every `x` with `|pi(x)| >= R`,
   `tau(o,x) <= sum_{y in pi^(-1)(S_Q(R))} tau(o,y) tau(y,x)`;
4. `sum_x tau(o,x) = infinity` and `sum_q sigma(q)^2 < infinity`;
5. `N(sigma 1_{S_Q(R)}) >= 4` for every `R >= 1`, and `N(sigma) = infinity`.

*Proof.* Put `W = coth(alpha/2) = sum_m e^(-alpha|m|)`, so `sigma(q) = W f(|q|)` and
`W > coth(alpha) >= 3`.
1. `f(0) = 1` and `f` is decreasing. Inversion preserves `|q|` and `|m|`.
2. The height factor satisfies `e^(-alpha|m+m'|) >= e^(-alpha|m|) e^(-alpha|m'|)`.
   Since `f` decreases and `|qq'| <= |q| + |q'|`, it suffices that
   `f(n+n') >= f(n) f(n')`. That is `(2+n)(2+n') >= 2(2+n+n')`, i.e. `nn' >= 0`.
3. For `R = 0` take `y = o`. Let `R >= 1`, `x = (q,m)` and `|q| = n >= R`.
   * **Heights.** Summing over heights `m'`: the `|m|+1` values between `0` and `m`
     each give `e^(-alpha|m|)`. The two tails give `e^(-alpha|m|) sum_{k>=1} e^(-2 alpha k)`
     each. So the height sum is at least `e^(-alpha|m|) coth(alpha) >= 3 e^(-alpha|m|)`.
   * **Sphere.** `S_Q(R)` contains the length-`R` prefix of `q`, at distance `n - R`
     from `q`. For `1 <= j <= R-1` it contains `2 * 3^(j-1)` elements that follow `q`
     for `R - j` letters and then leave it, each at distance `n - R + 2j` from `q`.
   * **Sum.** The right side is at least

         3 f(R) [ f(n-R) + sum_{j=1}^{R-1} 2*3^(j-1) f(n-R+2j) ] e^(-alpha|m|)
           = 12 * 3^(-n/2) (2+R)^(-1) [ (2+n-R)^(-1) + (2/3) sum_{j=1}^{R-1} (2+n-R+2j)^(-1) ] e^(-alpha|m|)
           >= 4 (2R+1) 3^(-n/2) / ((2+R)(2+n+R)) * e^(-alpha|m|).

   * **Compare.** `tau(o,x) = 2 * 3^(-n/2) e^(-alpha|m|) / (2+n)`. Since `n >= R`,
     `2+n+R <= 2(2+n)`, so it suffices that `2R+1 >= 2+R`, which holds for `R >= 1`.
4. `sum_x tau(o,x) = W (1 + sum_{n>=1} 4*3^(n-1) * 2 * 3^(-n/2)/(2+n)) = infinity`, and
   `sum_q sigma(q)^2 = W^2 (1 + (16/3) sum_{n>=1} (2+n)^(-2)) < infinity`.
5. Haagerup's spherical function `phi_0(q) = (1 + |q|/2) 3^(-|q|/2)` on `F_2` is
   positive definite, has `phi_0(1) = 1`, and is a coefficient of a representation
   weakly contained in `lambda`. So `N(g) >= sum_q g(q) phi_0(q)` for finitely
   supported `g >= 0`. For `g = sigma 1_{S_Q(R)}` the sum is
   `4*3^(R-1) * W * 2 * 3^(-R/2)/(2+R) * (1+R/2) 3^(-R/2) = (4/3) W >= 4`.
   Summing over spheres, `N(sigma 1_{B_Q(R)}) >= (4/3) W R`, which is unbounded. QED.

The kernel behaves like a Green function at the bottom of the spectrum,
`sigma ≍ (1+|q|)^(-1) 3^(-|q|/2)`, and not like the mean-field profile at `z = 1`.
Single-kernel inequalities cannot tell critical percolation apart from this
profile. A proof of (a) must use how `sigma_p` changes with `p` (Russo's formula,
the susceptibility exponent), or geometry beyond (F1). The same construction
should work over any non-elementary hyperbolic quotient, using Coornaert's
sphere estimates and Harish-Chandra-type estimates. That version is not written
out here.

## 5. Horofunction tilting does not transfer as it stands

Hutchcroft's nonunimodular proof (arXiv:1711.02590) rests on three ingredients:
* separating layers `{log Delta = t}`, which every path crosses;
* supermultiplicative upward crossing probabilities, whose exponential rate
  passes to `p_c` by Fekete's lemma and left-continuity (Section 5 there,
  `lem:alpha`, `lem:probinfsup`, `lem:alphacontinuity` in the arXiv source);
* the Schur test with weight `Delta^(1/2)`, which gives `||T_p|| <= chi_{p,1/2}`.

Over a hyperbolic `Q` the natural substitutes are horofunctions `h` on `Q`,
pulled back to `X`, with a Patterson–Sullivan measure `nu` on `dQ`.
* **Cuts and supermultiplicativity survive.** Every path crosses the level sets of
  `h o pi`. Take the infimum, over horofunctions normalized at `o`, of
  `P_p(o <-> {h >= t} inside {h >= 0})`. It is supermultiplicative by the
  exploration argument of `lem:alpha`, because translates of normalized
  horofunctions are again normalized horofunctions.
* **Infimum and supremum over directions are not comparable.** `lem:probinfsup`
  compares best and worst starting points through level-preserving automorphisms.
  The level-preserving elements of `Q` fix a boundary point, so they form a
  virtually cyclic or trivial group, and no such comparison is available. The
  rate from the infimum bounds only the worst direction.
* **The averaged tilt points the wrong way.** The `nu`-average of the half-tilted
  susceptibility is `sum_q sigma_p(q) Xi(q)`, with
  `Xi(q) = int (d(q_* nu)/d nu)^(1/2) d nu`. `Xi` is a coefficient of the boundary
  representation, which is weakly contained in `lambda_Q` because the boundary
  action is amenable. So the average is at most `N(sigma_p)`. A Schur test for the
  fibre operator needs the supremum over directions, not the average.

These points are analysis, not theorems. They record where the method must change.

## 6. A source check

Section 7(c) of `research/artifacts/fpbs/docs/benjamini-schramm-frontier-map.md`,
as landed in 4154fd4c6, used a critical bound `tau_{p_c}(u,v) <= gr(G)^(-d(u,v)/2)`
and marked it as still being checked. Commit 15d81ea51 replaced it with the
infimum statement below, and this independent reading of the source agrees. The
source is Hutchcroft arXiv:1605.05301v1, whose Theorem 2 (page 2) states

    kappa_{p_c}(n) := inf{ tau_{p_c}(x,y) : x, y in V, d(x,y) <= n }  <=  gr(G)^(-n).

That is an infimum over pairs. It is proved from supermultiplicativity of
`kappa_p` (Lemma 4), left-continuity (Lemma 5) and `kappa_p(n) |B(rho,n)| <= chi_p`.
The paper states no supremum bound on `tau_{p_c}(u,v)`, so that source does not
support that estimate. Over a quotient, the infimum argument
transfers only to the fibre maxima `mu_p(q) = sup_{x in Gamma_q} tau_p(o,x)`,
which are supermultiplicative. Fibre sums are not supermultiplicative.

## 7. Graph changes and trust surfaces

* New established claim `fpbs-sphere-fibre-operator-iff-critical-fibre-l2`
  (Theorem A and Corollary B), with route
  `fpbs-sphere-fibre-operator-iff-fibre-l2-proof`.
* Attempts added to `fpbs-critical-sphere-fibre-operator-below-one`: the
  equivalence, Proposition C, Proposition D and Section 5.

**Not verified.**
* The corollary (F5) of arXiv:1804.10191 was read from the arXiv LaTeX source on
  MSI. Proposition 2.4 and Remark 2.3 of arXiv:1904.05804 were read from the arXiv
  v2 PDF, pages 6–8. Theorem 2 of arXiv:1605.05301 was read from the v1 PDF, page 2.
* Haagerup's spherical function on `F_2`, and its weak containment in `lambda`, are
  imported (Haagerup 1979; Figà-Talamanca–Picardello). They were not re-read.
* Novelty is not checked. The hard direction of Theorem A is Hutchcroft's
  Proposition 2.4 run on fibre sums.
