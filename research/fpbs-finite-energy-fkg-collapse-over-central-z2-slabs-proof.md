---
rg: 2
id: fpbs-finite-energy-fkg-collapse-over-central-z2-slabs-proof
kind: route
title: Thin amenable Z2 slabs to their Burton--Keane giants, join them by connectors recurring along the central direction, and absorb detached finite pieces into critical Bernoulli
target: fpbs-finite-energy-fkg-collapse-over-central-z2-slabs
requires:
  - fpbs-critical-no-infinite-cluster
  - fpbs-simple-generating-set-with-gap-exists
---

Notation as in the target. `G = Cay(Gamma,S)` is unimodular, so the
mass-transport principle (MTP) holds. Put `Delta = |S|+1`, so `|B_r| <= Delta^r`.
Left multiplication is a graph automorphism. For a word `w = s_1...s_l`,
`P(v,w)` is the path `v, v s_1, ..., v s_1...s_l`, and `gamma P(v,w) = P(gamma v,w)`.
Fix `S`-words `w_g`, `w_t` for `g`, `t` and let `L = max(|w_g|,|w_t|)`.
Absolute continuity is used throughout in this form: if `X'` is obtained from `X`
by replacing finitely many independent coordinates with independent draws whose
laws have bounded density with respect to the original marginals, then every
a.s. property of `X` holds a.s. for `X'`.

## 0. Cosets and slabs

`H = <g,t> ≅ Z^2`. For a left coset `c = xH` its *core* is the vertex set
`c`, and `[v] = vH`. Cores partition `V(G)`. `Gamma` acts on `Gamma/H` by
`gamma xH = gamma x H`. Since `t` is central, `t c = x t H = c` for every `c`.
The index `[Gamma:H]` is infinite, because `H` is amenable and `Gamma` is not.

**Slab.** `S_c = ∪_{v in c} (P(v,w_g) ∪ P(v,w_t))`. This is a subgraph of `G`
with `gamma S_c = S_{gamma c}`. Every vertex of `S_c` is within distance `L` of
`c`. The core `c` is joined along the `g`-paths and `t`-paths, since
`x g^i t^m · g = x g^{i+1} t^m`, so `S_c` is connected. The subgroup
`x H x^{-1} ≅ Z^2` acts on `S_c` by left multiplication. It acts freely on
vertices, with finitely many orbits of vertices and edges.

**Lemma 1 (slab percolation).** There is `q_0 < 1`, independent of `c`, such
that for `q in (q_0,1)` Bernoulli(`q`) bond percolation on `S_c` has a.s.
exactly one infinite cluster `J_c`. Moreover `P(u in V(J_c)) > 0` for every
`u in V(S_c)`.

*Proof.*

*Amenable.* `S_c` carries a free cocompact action of `Z^2`, so it is
quasi-isometric to `Z^2`. Hence it is amenable.

*Uniqueness.* The percolation is invariant under a quasi-transitive group of
automorphisms and is insertion tolerant. The Burton–Keane theorem for amenable
quasi-transitive graphs (Lyons–Peres, *Probability on Trees and Networks*,
Ch. 7) gives at most one infinite cluster.

*Existence.* Identify `c` with `Z^2` by `(i,m) -> x g^i t^m`. Declare the macro
edge `((i,m),(i+1,m))` open when every edge of `P(x g^i t^m, w_g)` is open, and
treat vertical macro edges the same way with `w_t`. Each macro edge is open with
probability at least `q^L`. Suppose two macro paths share an edge. Their base
points `xh`, `xh'` satisfy `|h^{-1}h'|_S <= 2L`. Only finitely many `h'' in H`
have `|h''|_S <= 2L`, so the macro field is finite-range dependent on `Z^2`.
By Liggett–Schonmann–Stacey (Ann. Probab. 25 (1997), Thm 0.0), it dominates
Bernoulli(`pi(q^L)`) bond percolation on `Z^2`, and `pi(p) -> 1` as `p -> 1`.
Choose `q_0` with `pi(q_0^L) > 1/2`. Then the macro field percolates, and an
open macro path is an open path of `S_c`. The constant `q_0` depends only on the
finite data of `H`, `w_g`, `w_t`, since `S_{xH} = x S_H`.

*Positive probability.* Let `B^K_r(u)` be the ball in the intrinsic metric of
`S_c`. Pick `r` with `P(V(J_c) ∩ B^K_r(u) ≠ ∅) > 0`. The events
{all edges of `B^K_r(u)` are open} and {`J_c` meets `B^K_r(u)`} are increasing,
and their intersection lies in {`u in V(J_c)`}. By Harris,
`P(u in V(J_c)) >= q^{|E(B^K_r(u))|} · P(J_c meets B^K_r(u)) > 0`. ∎

Fix `q in (q_0,1)`.

## 1. Construction

All of the following variables are independent.

* `U_e`, uniform on `[0,1]`, for `e in E(G)`.
* `B_e`, Bernoulli(`q`), for `e in E(G)`. This is the thinning.
* `sigma^k_c`, Bernoulli(`2^-k`), for `k >= 1` and `c in Gamma/H`. This is
  the selection.
* `lambda^k_{v,c'}`, Bernoulli(`Delta^{-3 d(v,c')}`), for `k >= 1`,
  `v in V(G)` and `c' ≠ [v]`, where `d(v,c') = min_{u in c'} d(v,u) >= 1`.

`Gamma` permutes the index sets, so the joint law `P` is invariant.

* `J_c` is the infinite cluster of `{e in E(S_c) : B_e = 1}`. Put `J_c = ∅` on
  the null event where it is not unique.
* `N(v,c')` is the set of `u in c'` with `d(v,u) = d(v,c')`. It is finite,
  because `G` is locally finite. `Q(v,c')` is the union of all `S`-geodesics
  from `v` to points of `N(v,c')`. It is a finite connected subgraph containing
  `v` and `N(v,c')`, and it lies in `B_{d(v,c')}(v)`.
* The pair `(v,c')` is *admissible at level `k`* if all of the following hold:
  1. `lambda^k_{v,c'} = 1`;
  2. `sigma^k_{[v]} = 1`;
  3. `sigma^k_{c'} = 1` or `sigma^{k+1}_{c'} = 1`;
  4. `B_f = 1` for every edge `f` of `Q(v,c')`;
  5. `v in V(J_{[v]})` and `N(v,c') ⊆ V(J_{c'})`.
* `W_k = ∪_{c : sigma^k_c = 1} J_c ∪ ∪_{(v,c') admissible at level k} Q(v,c')`.
* `eta_n = ∪_{k >= n} W_k`. This is decreasing in `n`.
* `omega_t = xi_t` for `t <= p_c`, and `omega_t = xi_{p_c} ∪ eta_{n(t)}` for
  `t > p_c`, with `n(t) = ceil(1/(t-p_c))`.

The configurations `eta_n` do not depend on `U`.

## 2. Densities

**Lemma 2.** For every vertex `o` and every `k`:

* (a) `P(o in V(J_c) for some c with sigma^k_c = 1) <= Delta^L 2^-k`;
* (b) `E #{(v,c') : lambda^k_{v,c'} = 1, sigma^k_{[v]} = 1, o in V(Q(v,c'))} <= 2^-k`.

Hence `P(o in V(W_k)) <= (Delta^L + 1) 2^-k`, and `P(o in V(eta_n)) <= (Delta^L+1) 2^{1-n}`.
Also, a.s. every vertex lies in `V(W_k)` for only finitely many `k`, and lies on
only finitely many connectors `Q(v,c')` with `lambda^k_{v,c'} = sigma^k_{[v]} = 1`,
summed over `k`.

*Proof.*

*(a)* If `o in V(S_c)`, then `c = [u]` for some `u in B_L(o)`. There are at
most `Delta^L` such `c`, each selected with probability `2^-k`.

*(b)* Put `f(v,o) = E sum_{c'} 1[lambda^k_{v,c'} = sigma^k_{[v]} = 1] 1[o in V(Q(v,c'))]`.
This is diagonally invariant. A coset `c'` with `d(v,c') = d` contains a vertex
at distance `d` from `v`, so there are at most `Delta^d` such cosets. Also
`|V(Q(v,c'))| <= Delta^d`. So
`sum_o f(v,o) <= 2^-k sum_{d >= 1} Delta^d · Delta^{-3d} · Delta^d <= 2^-k`.
The MTP gives `sum_v f(v,o) = sum_o f(o,v) <= 2^-k`, which is (b).

The last sentence follows from Borel–Cantelli, since `sum_k 2^-k < infinity`. ∎

## 3. Connectivity

**Lemma 3.** A.s., for every `n`, the subgraph `eta_n` is connected and infinite,
and it contains `J_c` for every `c` selected at some level `k >= n`.

*Proof.*

*Setup.* Condition on `sigma`. The other variables `Y = (U,B,lambda)` stay
i.i.d. and are independent of `sigma`. Left multiplication by `t` sends
`e -> te` and `(v,c') -> (tv,c')`, since `t c' = c'`. It has no finite orbits on
these index sets, because `t` has infinite order and acts freely on vertices. So
it acts on `Y` as a Bernoulli `Z`-shift, which is mixing and hence ergodic. It
fixes `sigma`, maps `S_c` to itself, and maps `J_c(Y)` to `J_c` of the shifted
configuration.

*One pair of cosets.* Fix `k`, `c`, `c'` with `sigma^k_c = 1` and
`sigma^k_{c'} ∨ sigma^{k+1}_{c'} = 1`. Fix `v in c`. Let `E_0` be the event
that `lambda^k_{v,c'} = 1`, that `B = 1` on `Q(v,c')`, that `v in V(J_c)`, and
that `N(v,c') ⊆ V(J_{c'})`. Let `E_h` be its translate by `t^h`. Here
`d(t^h v, c') = d(v,c')` and `Q(t^h v, c') = t^h Q(v,c')`, so `E_h` is the same
event for the pair `(t^h v, c')`.

*Positive probability.* All four events are increasing in `(B,lambda)`, and
`v`, `N(v,c')` are vertices of the slabs. By Harris and Lemma 1,
`P(E_0 | sigma) >= Delta^{-3d} q^{|E(Q)|} P(v in V(J_c)) · P(N ⊆ V(J_{c'})) > 0`.
The last factor is positive by Harris again, as a product over the finitely many
points of `N`.

*Recurrence.* By Birkhoff's theorem, `(1/M) sum_{h<M} 1_{E_h} -> P(E_0|sigma) > 0`
a.s. So some `E_h` occurs. Then `(t^h v, c')` is admissible at level `k`, and
`Q(t^h v, c') ⊆ W_k` joins `J_c` to `J_{c'}`. This holds for all countably many
such pairs simultaneously.

*Assembly.* For each `k`, infinitely many cosets are selected at level `k`
a.s., and each `J_c` is infinite. Take `c`, `c''` selected at levels
`n <= k <= k''`. Choose `c_j` selected at level `j` for `k < j <= k''`. Then
`J_c`, `J_{c_{k+1}}`, ..., `J_{c_{k''}}`, `J_{c''}` are successively joined by
connectors of the levels `k, ..., k''-1, k''`, all of which belong to `eta_n`.
Every admissible connector at a level `k >= n` meets `J_{[v]}` at `v`, and
`[v]` is selected at level `k`. So `eta_n` is connected. ∎

## 4. (S1)–(S4)

* **(S1), (S2).** These hold by construction.
* **(S4).** Fix `t > p_c` and `n = n(t)`. By `fpbs-critical-no-infinite-cluster`,
  all clusters of `xi_{p_c}` are finite a.s.
  * *Uniqueness.* A component of `omega_t` with no edge of `eta_n` is a cluster
    of `xi_{p_c}`, so it is finite. Every infinite component therefore contains
    the connected infinite `eta_n` (Lemma 3). So there is exactly one.
  * *`theta -> 0`.* `theta(t) <= P(C_{xi}(o) ∩ V(eta_{n(t)}) ≠ ∅)`. The cluster
    `C_{xi}(o)` is finite. By Lemma 2, each of its vertices lies in finitely
    many `V(W_k)`, so the intersection is eventually empty. Dominated
    convergence gives `theta(t) -> 0`.
* **(S3), insertion tolerance.** Use the argument of sw-008 verbatim. Replace
  `U_e` by `1`, and use `U_e <= min(t,p_c)`. It only needs `eta` to be
  independent of `U`.
* **(S3), ergodicity.** `(U,B)` and `lambda` are Bernoulli shifts over actions
  with finite stabilizers, so they are mixing and hence weakly mixing. For each
  level `k`, `sigma^k` is a generalized Bernoulli shift over
  `Gamma -> Sym(Gamma/H)`. All orbits of that action are infinite, so it is
  weakly mixing (Kechris–Tsankov, Proc. AMS 136 (2008), Prop. 2.1). A countable
  product of weakly mixing actions is weakly mixing. So the joint action is
  ergodic, and so is its factor `omega_t`.
* **Not a product.** `P(e in omega_t) <= p_c + P(an endpoint of e is in V(eta_{n(t)})) -> p_c`.
  A Bernoulli(`r`) configuration with a unique infinite cluster needs
  `r >= p_u`. On a graph with `p_c < p_u`, `omega_t` is not a product measure
  for `t` close to `p_c`.

## 5. (S5) Deletion tolerance

For `t <= p_c` it is immediate. Fix `t > p_c`, `n = n(t)` and an edge `e`. Let
`X` be all the variables, and let `X^e` be `X` with `B_e` set to `0`.

**Lemma 4.** A.s. `D := eta_n(X) \ eta_n(X^e) \ {e}` is finite. Also
`eta_n(X^e) ⊆ eta_n(X) \ {e}`.

*Proof.*

*Inclusion.* Monotonicity gives `eta_n(X^e) ⊆ eta_n(X)`. The edge `e` is in no
`J_c(X^e)` and in no admissible connector of `X^e`, because condition 4 fails.

*Slabs.* The law of `X^e` is absolutely continuous with respect to that of `X`,
with density at most `1/(1-q)`. So Lemma 1 and Lemma 2 hold for `X^e`. Only the
`<= Delta^L` slabs containing `e` change. For such a slab with `e in J_c(X)`,
removing `e` from `J_c(X)` leaves at most two components. The unique infinite
cluster `J_c(X^e)` is one of them. If the other were infinite, `X^e` would have
two infinite clusters in `S_c`, which is a null event. So
`J_c(X) \ J_c(X^e) \ {e}` is a finite component `F_c`.

*Connectors.* An admissible pair of `X` at some level `k >= n` that is not
admissible for `X^e` has `e in Q(v,c')`, or has `v` or a point of `N(v,c')` in
`V(F_c) ∪ e`. Every such connector has a vertex in the finite set
`∪_c V(F_c) ∪ e`. By Lemma 2 there are finitely many such connectors a.s. ∎

**Deletion tolerance.** Let `P(omega_t in A) > 0`. The event splits by the value
of `D`, and there are countably many finite `F ⊂ E(G) \ {e}`. So some `F` has
`P(A_F) > 0`, where `A_F = {omega_t(X) in A, D(X) = F}`.

*Coordinates.* Split `X = (X_loc, X_rest)`, with `X_loc = (B_e, U_e, (U_f)_{f in F})`.
The set `D`, and `eta_n` of both `X` and `X^e`, depend on `X_loc` only through
`B_e`, and the definition of `D` already puts `B_e = 0` in `X^e`. By Fubini, the
set `R = {x_rest : P(X in A_F | X_rest = x_rest) > 0}` has `P(X_rest in R) >= P(A_F) > 0`.

*Target configuration.* Take `x_rest in R` and `y_loc` in the box
`{B_e = 0, U_e > p_c, U_f <= p_c for f in F}`. Pick any `x = (x_loc, x_rest) in A_F`,
and put `y = (y_loc, x_rest)`. Then:

* `eta_n(y) = eta_n(x^e)`;
* `xi_{p_c}(y) = (xi_{p_c}(x) \ {e}) ∪ F`;
* `eta_n(x) = eta_n(x^e) ∪ F ∪ ({e} ∩ eta_n(x))`.

Hence `omega_t(y) = omega_t(x) \ {e} in Pi_{¬e} A`.

*Conclusion.* `X_loc` and `X_rest` are independent, so
`P(omega_t in Pi_{¬e} A) >= P(X_rest in R) · (1-q)(1-p_c) p_c^{|F|} > 0`. ∎

## 6. (S6) Harris–FKG

Each `omega_t` is a function of the independent coordinates `(-U, B, sigma, lambda)`.
It is increasing in them:

* `1[U_e <= p_c]` is decreasing in `U_e`;
* `J_c` is increasing in `B`;
* admissibility is an AND of increasing conditions: `lambda`, the `sigma`
  conditions (with an OR inside), `B` on `Q`, and membership in increasing `J`s;
* unions preserve monotonicity.

The Harris inequality for bounded increasing measurable functions of countably
many independent totally ordered coordinates follows from the finite case by
martingale convergence. So every pair of increasing events of `omega_t` is
positively correlated. ∎

## 7. Corollary

* **Membership.** `Gamma = F_2 x Z` with `t = (1,1)` and `g = (a,0)` is in `Z`.
* **A true window.** `fpbs-simple-generating-set-with-gap-exists` supplies a
  Cayley graph of `Gamma` with `p_c < p_u`.
* **The argument.** Suppose a proof of `p_c < p_u` uses only the inputs listed
  in the target. It then applies verbatim to the family `omega_t` of Sections
  1–6 on that graph, and concludes that `omega_t` has two or more infinite
  clusters for some `t > p_c`. This contradicts (S4). So such a proof does not
  exist. ∎
