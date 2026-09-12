# Fibre-summed connectivity and hyperbolic quotients

Lane `bs-pc-pu`, 2026-09-12. The target is `p_c < p_u` on every Cayley graph of
a group with an infinite normal subgroup whose quotient is hyperbolic. This
covers `F_2 x Z` (Choi–Seo arXiv:2508.08932v2, Question 1.3), Seifert-fibred
groups with hyperbolic base (Question 1.6), `Gamma x Z^k` with `Gamma`
hyperbolic, and `F_2 x F_2`.

This note carries Hutchcroft's hyperbolic proof (arXiv:1804.10191, Sections 2
and 5) over to this class, with the whole argument run on the quotient. It
proves three things:

1. The connectivity operator is bounded by its fibre-summed version on the
   quotient, with equality when the normal subgroup is amenable.
2. A uniform bound on one fibre diagram, the fibre bubble, gives the mean-field
   susceptibility bound.
3. That bound together with a far-halfspace estimate gives `p_c < p_{2->2}`,
   hence `p_c < p_u`.

The two fibre estimates stay open. Nothing here is refereed or formalized.
Hutchcroft's geometric inputs are imported, not reproved.

## 0. Setting and notation

`Gamma` is finitely generated. `S` is a finite symmetric generating set,
`X = Cay(Gamma,S)`, `d = |S|`, and `o` is the identity. `H` is a normal
subgroup of `Gamma`, `Q = Gamma/H`, `pi : Gamma -> Q` the quotient map, and
`Gamma_q = pi^(-1)(q)` the fibres. `tau_p(x,y) = P_p(x <-> y)` is the two-point
function, `T_p` its matrix, `chi_p = E_p|K_o|`, and `A` the adjacency matrix.

Define the **fibre-summed two-point function**, the **fibre operator** on
`l2(Q)`, the **fibre bubble** and the relative susceptibility:

    sigma_p(q) = sum_{x in Gamma_q} tau_p(o,x) = E_p|K_o ∩ Gamma_q|,
    (S_p F)(q) = sum_{q'} sigma_p(q^(-1) q') F(q'),
    B^H_p      = sum_{q in Q} sigma_p(q)^2,
    chi^H_p    = sigma_p(1).

Elementary facts, used throughout:

* (a) `sigma_p(q^(-1)) = sigma_p(q)`, because `tau_p(o,x^(-1)) = tau_p(x,o)`.
* (b) For `u in Gamma_q`, `sum_{v in Gamma_(q')} tau_p(u,v) = sigma_p(q^(-1)q')`,
  since `u^(-1) Gamma_(q') = Gamma_(q^(-1) q')`. This uses normality.
* (c) `sum_q sigma_p(q) = chi_p`, so `S_p / chi_p` is symmetric and stochastic
  when `chi_p < infinity`.
* (d) `max_q sigma_p(q) <= (B^H_p)^(1/2)`, and `B^H_p >= 1`.

## 1. Fibre summation of the connectivity operator

**Theorem 1.1.** For every `p in [0,1]`, `||T_p||_(2->2) <= ||S_p||_(2->2)` in
`[0,infinity]`. If `H` is amenable, the two are equal.

*Proof of the inequality.* Let `f, g` be finitely supported on `Gamma`, and put
`F(q) = ||f|_(Gamma_q)||_2` and `G(q) = ||g|_(Gamma_q)||_2`. For `q, q'`, the
block `(tau_p(u,v))_(u in Gamma_q, v in Gamma_(q'))` has every row sum equal to
`sigma_p(q^(-1)q')` by (b). Its column sums are `sigma_p(q'^(-1)q)`, which is the
same number by (a). Schur's test bounds the block's norm by `sigma_p(q^(-1)q')`.
Summing over blocks,

    |<f, T_p g>| <= sum_{q,q'} sigma_p(q^(-1)q') F(q) G(q') = <F, S_p G>
                 <= ||S_p|| ||f||_2 ||g||_2.

*Proof of equality for amenable `H`.* Write `tau_p(g) = tau_p(o,g)`. Then
`(T_p f)(x) = sum_g tau_p(g) f(xg)`, so `T_p = rho_Gamma(tau_p)` for the right
regular representation. Likewise `S_p = (rho_Q o pi)(tau_p)`, and `rho_Q o pi`
is the quasi-regular representation on `l2(Gamma/H)`. When `H` is amenable,
`1_H` is weakly contained in `lambda_H`. Induction preserves weak containment,
so `lambda_(Gamma/H) = Ind 1_H` is weakly contained in `Ind lambda_H = lambda_Gamma`.
Hence `||(rho_Q o pi)(phi)|| <= ||rho_Gamma(phi)||` for every finitely supported
`phi >= 0`. Apply this to the truncations `tau_p 1_(B_n)` and let `n -> infinity`.
Both operator norms are monotone limits over finitely supported test vectors,
so `||S_p|| <= ||T_p||`. QED.

**Corollary 1.2.** Let `H` be amenable.
* `chi^H_p = <delta_1, S_p delta_1> <= ||T_p||` and `B^H_p = ||S_p delta_1||^2 <= ||T_p||^2`.
* Hutchcroft's L2 condition `||T_(p_c)|| < infinity` on `Cay(Gamma,S)` is
  equivalent to boundedness of the fibre operator `S_(p_c)` on `l2(Q)`.

So for `F_2 x Z` the L2 conjecture is a statement about one nonnegative kernel
on the free group.

## 2. The fibre bubble gives the mean-field susceptibility bound

**Theorem 2.1.** Let `Q` be non-elementary word hyperbolic and suppose

    B := sup_{p < p_c} B^H_p < infinity.

Then there is `C < infinity` with `chi_p <= C (p_c - p)^(-1)` for all `p < p_c`.

Imported inputs. They are stated for `G_Q = Cay(Q, pi(S) \ {1})`, which is
hyperbolic.

* **(H1) Supporting hyperplanes.** Hutchcroft arXiv:1804.10191, Corollary 4.3;
  Choi–Seo Proposition 2.7. There is `r` such that every finite `A` in `Q` has a
  subset `A'` with `|A'| >= |A|/2` and the following property: for each `a` in
  `A'` there is `b` with `d(a,b) <= r`, the discrete halfspace
  `H_Q(a,b) = {q : d(q,a) <= d(q,b)}` proper, and `A` contained in `H_Q(a,b)`.
* **(H2) Separated translates.** Hutchcroft Lemma 3.6 and its proof. For a
  proper halfspace `H_Q`, `g^n H_Q` lies in a boundary neighbourhood disjoint
  from the closure of `H_Q` for all large `n`, with `g` hyperbolic. So for each
  of the finitely many halfspaces `H_Q(1,b)` with `d(1,b) <= r` we can fix
  `g_b in Q` with `d_Q(H_Q(1,b), g_b H_Q(1,b)) >= 2`. Fix a lift `gamma_b` in
  `Gamma` and an X-geodesic `eta_b` from `o` to `gamma_b`.
* **(H3) Tree-graph inequality** (Aizenman–Newman):
  `P(o <-> x, o <-> y) <= sum_w tau(o,w) tau(w,x) tau(w,y)`.
* **(H4) Mass-transport principle** on `Gamma` under left multiplication.

**Lemma 2.2 (clusters meet many fibres).** For `p < p_c`,
`E_p|pi(K_o)| >= chi_p / (4B)`.

*Proof.* Let `K = K_o` and `m(q) = |K ∩ Gamma_q|`. Fix `M >= 1`.
* Points of `K` on fibres with `m(q) >= M` number at most `sum_q m(q)^2 / M`.
* The remaining points lie on fibres with `m(q) < M`, and there are at least
  `(|K| - sum_q m(q)^2 / M) / M` such fibres.
* Hence `|pi(K)| >= (|K| - sum_q m(q)^2/M)/M`.

Now `sum_q m(q)^2 = sum_(v in K) |K ∩ vH|`. The transport
`F(x,y) = 1{y in K_x} |K_x ∩ yH|` is diagonally invariant, so (H4) gives
`E sum_q m(q)^2 = E[|K_o| |K_o ∩ H|]`. By (H3) and (b),

    E[|K_o||K_o ∩ H|] <= sum_w tau(o,w) chi_p sum_(h in H) tau(w,h)
                       = chi_p sum_q sigma_p(q) sigma_p(q^(-1)) = chi_p B^H_p.

Take `M = 2B`: `E|pi(K_o)| >= (chi_p - chi_p/2)/(2B)`. QED.

**Lemma 2.3 (lifted supporting halfspace).** Let `N_r = |B_Q(1,r)|`. For every
`p < p_c` there is `b = b_p` with the following properties:
* `d(1,b) <= r`;
* `H_Q(1,b)` is proper;
* `E_p[ |K_o| 1{pi(K_o) ⊆ H_Q(1,b)} ] >= chi_p / (8 B N_r)`.

*Proof.* For `x` in `Gamma` and finite `K`, let `I(x,K) = 1` when some `b` with
`d(pi(x),b) <= r` makes `H_Q(pi(x),b)` proper and contains `pi(K)`.
* Apply (H1) to `pi(K)`. Every point of `A'` has at least one lift in `K`, so
  `sum_(x in K) I(x,K) >= |pi(K)|/2`.
* By (H4) and Lemma 2.2, `E[|K_o| I(o,K_o)] = E sum_(x in K_o) I(x,K_o) >= chi_p/(8B)`.
* A union bound over the `N_r` choices of `b` gives the claim. QED.

This is the only point where the argument differs from Hutchcroft's Lemma 5.3.
His deterministic condition, "half of every finite set is supported", fails
for `Gamma` itself when the set is concentrated on one fibre; Choi–Seo Section
2.3 gives exactly this example for `F_2 x Z`. The lemma counts fibres met rather
than points. The fibre bubble is what converts that count back into
susceptibility.

*Proof of Theorem 2.1.* This follows Hutchcroft's proof of Proposition 5.1; see
also Choi–Seo Appendix A. Fix `p in [p_c/2, p_c)`, let `b = b_p`, and put
`H = pi^(-1) H_Q(1,b)` and `gamma = gamma_b`.

1. Since `pi` is 1-Lipschitz, `d_X(H, gamma H) >= 2`, so no edge meets both
   sets. The event `{|K_o| = n, K_o ⊆ H}` is measurable with respect to edges
   with an endpoint in `H`, and the same holds for `gamma H`. The two events
   are therefore independent, and by Lemma 2.3
   `E[|K_o||K_gamma| 1{K_o ⊆ H, K_gamma ⊆ gamma H}] >= (chi_p/(8BN_r))^2`.
2. A finite-energy modification along `eta_b` gives
   `E[|K_(e-)||K_(e+)| 1{e- <-/-> e+}] >= c_p E[...]`. Here `e` is the first
   edge of `eta_b` leaving `H`, and `c_p` is bounded below on `[p_c/2,p_c]`.
   This is Hutchcroft (5.4). The modification opens `eta_b` minus `e`, closes
   `e`, and closes the incident edges not already joined to the two clusters.
3. Russo's formula with mass transport gives
   `d^+ chi_p / dp >= (1/(1-p)) sum_(s in S) E[|K_o||K_s| 1{o <-/-> s}]`. This is
   Hutchcroft (5.2).
4. The pair `(b, e)` ranges over finitely many types. So
   `d^+ chi_p/dp >= C^(-1) chi_p^2` on `[p_c/2,p_c)`.
5. Integrate from `p` to `p_c`, using `chi_(p_c) = infinity`. QED.

## 3. Two fibre estimates give p_c < p_{2->2}

Fix a rough similarity `Phi : Q -> Y ⊆ H^d` onto a coarsely dense subset of a
closed convex set. Such a map exists by Bonk–Schramm, as in Hutchcroft Section
3. The **far-halfspace share** is

    sh(D) = sup_{p<p_c} sup_{a in Q} sup_{H ⊆ H^d halfspace, d(Phi(a),H) >= D}
            chi_p^(-1) sum_{q in Phi^(-1)(H)} sigma_p(a^(-1) q).

**Theorem 3.1.** Let `Q` be non-elementary hyperbolic, with any normal `H`.
Suppose (i) `B < infinity` and (ii) `sh(D) -> 0` as `D -> infinity`. Then
`p_c(X) < p_{2->2}(X)`. Consequently `p_c < p_u` and `nabla_(p_c) < infinity`.

*Proof.* Since `S_p/chi_p` is symmetric and stochastic on `Q`, Cheeger's
inequality (Hutchcroft Lemma 2.8) gives `||S_p|| <= chi_p (1 - iota(S_p)^2)^(1/2)`,
where `1 - iota(S_p) = sup_A chi_p^(-1)|A|^(-1) sum_{q,q' in A} sigma_p(q^(-1)q')`
over finite `A` in `Q`.

Fix `eps > 0` and apply Hutchcroft's hyperbolic magic lemma (Proposition 4.1,
through `Phi`, as in his proof of Proposition 5.2). There are `N(eps)` and
`A' ⊆ A` with `|A'| >= (1-eps)|A|` such that each `a` in `A'` has halfspaces
`H_1, H_2` at distance `>= 1/eps` from `Phi(a)` with
`|A \ Phi^(-1)(H_1 ∪ H_2)| <= N(eps)`. By (d) and (ii),

    sum_{q,q' in A} sigma_p(q^(-1)q')
      <= |A \ A'| chi_p + |A'| (N(eps) B^(1/2) + 2 sh(1/eps) chi_p).

Hence `1 - iota(S_p) <= eps + N(eps) B^(1/2)/chi_p + 2 sh(1/eps)`. As `p` increases
to `p_c`, `chi_p -> infinity`, so `limsup (1 - iota(S_p)) <= eps + 2 sh(1/eps)`,
which tends to 0 as `eps -> 0`.

By Theorem 1.1, `||T_p|| <= ||S_p|| <= chi_p (2(1-iota(S_p)))^(1/2)`. By Theorem
2.1, `(p_c - p) chi_p <= C`. Therefore `(p_c - p)||T_p|| -> 0`. Hutchcroft's
Corollary 2.6 gives `||T_p|| >= (1-p)/(d (p_{2->2} - p))`, which rules out
`p_{2->2} = p_c`. Finally `p_{2->2} <= p_u`, and boundedness at `p_c` gives the
triangle condition. QED.

Amenability of `H` is not used in Sections 2 and 3. It enters only in the
equality half of Theorem 1.1 and in Corollary 1.2.

## 4. The premises, and where direct attacks stop

**4.1 Premise (i), the uniform fibre bubble.** It implies
`chi^H_(p_c) <= B^(1/2) < infinity`. It is implied by the L2 conjecture when `H`
is amenable (Corollary 1.2). Mean field predicts it: for critical branching
random walk, `sigma` is the Green function of the projected walk on `Q`, and
`||G_Q(1,.)||_2 <= sum_n rho(Q)^n < infinity`.

Russo plus BK give `dT_p/dp <= p^(-1) T_p A T_p` entrywise. Pushing forward,
`dB^H_p/dp <= (2d/p) ||S_p|| B^H_p`, so the bubble's derivative needs the L2
quantity itself. No bound on (i) without L2-type input was found.

**4.2 Premise (ii), the far-halfspace share.** Hutchcroft bounds the capacity of
nested roughly branching barriers (his Lemma 5.5) using supermultiplicativity
`tau(gh) >= tau(g) tau(h)`. Barriers for fibre-saturated sets must contain
whole fibres, and fibre sums are not supermultiplicative: products of lifts
collide in `H`.

What does survive, for central `H = <z>` with a section `s` and heights `n`:
* For a roughly branching set `B'` of `Q`, the fibre maxima
  `mu_p(b) = max_n tau_p(o, s(b) z^n)` satisfy `sum_(b in B') mu_p(b) <= 1`.
  The lifted products are distinct and FKG applies.
* Height windows `{s(b) z^n : b in B', |n| <= W}` have capacity at most `2W+1`.
  Each product value is hit at most `(2W+1)^(k-1)` times, and
  `chi_p >= cap^k / (2W+1)^(k-1)`.

Neither bounds a full-fibre barrier.

**4.3 Tree-projected generating sets.** Suppose `Q = F_n` and `pi(S) \ {1}`
lies in a free basis and its inverses, with arbitrary heights. Examples are
`{(a,0),(a,1),(b,0),(1,1)}` and their inverses in `F_2 x Z`. Every vertex of
`G_Q` is a cut vertex, so every fibre is a cut set of `X`. Sequential BK then
gives

    sigma_p(q) <= prod_(j=1)^(|q|) sigma_p(s_j),
    E_p|K_o ∩ pi^(-1)(branch at depth D)| <= (max_s sigma_p(s))^D chi_p,

where `s_1 ... s_(|q|)` is the geodesic word. So in this class (ii) follows from
`sup_(p<p_c) max_s sigma_p(s) < 1`, and (i) follows from bounded `chi^H_p` plus
`(2n-1) max_s sigma_p(s)^2 < 1`. The first of these is itself open. Also,
`sigma_p(s) >= p chi^H_p` by FKG.

With asymmetric height sets, no automorphisms beyond `Gamma` were found, so
Hutchcroft's nonunimodular theorem does not visibly cover these graphs. This
is a concrete subcase of Choi–Seo Question 1.3 with a cut structure.

**4.4 Tube excursions, and an exact criterion for tree-projected sets.** Let
`H` be infinite cyclic and normal, generated by `z`. Write
`b_R(p) = sum_{q in S_Q(R)} sigma_p(q)^2` for the fibre-sphere bubble, and
`T_r = pi^(-1)(B_Q(r))` for the tube.

*Lemma 4.1 (tube excursion bound).* Let `C_r(p) = E_p|K^(T_r)_o ∩ H|` be the
relative susceptibility of percolation restricted to the tube `T_r`. For every
`r >= 0` and every `p < 1`,

    chi^H_p <= C_r(p) + b_(r+1)(p),

and `C_r(p) < infinity` for every `p < 1`, increasing in `p`.

*Proof.* The group `H` acts on `T_r` by left multiplication with finitely many
orbits. Each vertex of `T_r` has a coarse coordinate `n` from
`x = s(q) z^n`, and edges change `n` by at most `L`. For each level `m`, the
edges of `T_r` crossing that level number at most `M_r`. Closing all of them
has probability at least `(1-p)^(M_r)`, and levels `2L` apart are independent.
So `P(o <-> z^n in T_r)` decays exponentially and `C_r(p) < infinity`.

If `o <-> z^n` but no open path lies inside `T_r`, take an open simple path
from `o` to `z^n`. Its first vertex `v` outside `T_r` has `|pi(v)| = r+1`,
because `pi(S)` lies in `B_Q(1)`. Splitting the path at `v` gives
`{o <-> v} ∘ {v <-> z^n}`. BK, summed over `v` and `n` using (b), gives
`sum_(|q|=r+1) sigma(q) sigma(q^(-1)) = b_(r+1)`. QED.

So divergence of relative susceptibility comes only from excursions to far
fibres, measured by one fibre-sphere bubble.

*Lemma 4.2 (submultiplicativity on a tree quotient).* Suppose
`Q = F_n`, `n >= 2`, and `pi(S) \ {1}` lies in a free basis and its inverses.
Then:
* `sigma_p(wu) <= sigma_p(w) sigma_p(u)` for reduced products `wu`;
* `b_(R+R')(p) <= b_R(p) b_(R')(p)`.

*Proof.* Every X-path from `o` to `Gamma_(wu)` passes through the cut fibre
`Gamma_w`. BK at the first visit gives `tau(o,x) <= sum_(v in Gamma_w) tau(o,v) tau(v,x)`.
Summing `x` over `Gamma_(wu)` gives the first inequality. Squaring and summing
over `|w| = R` and `|u| = R'` gives the second. QED.

*Theorem 4.3 (tree-projected equivalence).* In the setting of Lemma 4.2,

    p_c(X) < p_{2->2}(X)   if and only if   b_R(p_c) < 1 for some R.

In particular `p_c < p_u` follows from `b_R(p_c) < 1` for one finite radius `R`.

*Proof.*

(⇒) Let `p_c < p_{2->2}`. Corollary 1.2 gives
`sum_R b_R(p_c) = B^H_(p_c) <= ||T_(p_c)||^2 < infinity`, so `b_R(p_c) -> 0`.

(⇐) Suppose `b_(R_0)(p_c) = 1 - eta`.
1. `p -> sigma_p(q)` is nondecreasing and left-continuous, as a supremum of
   finite-volume connection probabilities. So `sup_(p<p_c) b_(R_0)(p) = 1 - eta`.
2. Lemma 4.1 with `r = R_0 - 1` bounds `chi^H_p <= C_(R_0-1)(p_c) + 1`
   uniformly for `p < p_c`.
3. Hence `b_j <= |S_Q(j)| (chi^H_p)^2` is bounded for each `j < R_0`.
   Lemma 4.2 gives `b_(k R_0 + j) <= (1-eta)^k b_j`.
4. So `B^H_p <= (sum_(j<R_0) b_j)/eta` uniformly: premise (i).
5. Also `max_(|w|=D) sigma_p(w) <= b_D^(1/2) -> 0` uniformly. A branch `beta_w`
   at depth `D` has share `E|K_o ∩ pi^(-1)beta_w| <= sigma_p(w) chi_p`, by BK
   through `Gamma_w`.
6. Far halfspaces pull back into a bounded number of branches at depth
   `>= D/lambda - C`. This is the shadow comparison for a convex-cocompact
   embedding of the tree in `H^2`. So `sh(D) -> 0`: premise (ii).
7. Theorem 3.1 applies. QED.

By submultiplicativity, the criterion is that the critical fibre-sphere bubble
decays exponentially: `beta = lim_R b_R(p_c)^(1/R) < 1`. Mean field predicts
`sigma(q) ≈ chi^H lambda^|q|` with `(2n-1) lambda = 1`, hence `beta = 1/(2n-1)`.
No proof of any finite-radius bound at `p_c` was found.

## 5. Not verified

* (H1), (H2), the magic lemma, and Hutchcroft's Lemma 2.8 and Corollary 2.6 are
  imported. They were read from the arXiv v3 text and not re-derived.
* The separated-translate refinement in (H2) is read off the proof of Lemma
  3.6, which pushes the halfspace into an arbitrarily small boundary
  neighbourhood.
* No numerics bear on (i) or (ii).
