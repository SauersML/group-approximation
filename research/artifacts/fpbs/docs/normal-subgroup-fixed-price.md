# Infinite normal subgroups of bounded cost: quotient-split actions, a Bernoulli obstruction, and the Burnside consequence

Written 2026-09-11 by the `fixed-price-1` lane. Evidence level: written
deductions from named published inputs; not refereed and not formally
verified. Nothing here settles `fpbs-fixed-price-universal`.

The note isolates one sharp open statement,
`fpbs-normal-subgroup-bounded-cost-fixed-price-one` (Section 3), proves the
case of it that the classical argument reaches (Theorem A), proves that this
case cannot be pushed to the Bernoulli shift by weak containment
(Proposition B), and shows that the open statement would decide the large odd
Burnside branch of the archive in the positive direction (Lemma 3.1 and
Consequence 3.2).

## 0. Setting and inputs

`Gamma` is a countable group, `N` a normal subgroup, `Q = Gamma/N`, and
`pi_Q : Gamma -> Q` the quotient map. Actions are probability measure
preserving on standard probability spaces; "free" means essentially free.
For a free action `alpha` of `Gamma` on `(X,mu)`, `R_alpha` is its orbit
relation and `R_alpha^N` the orbit relation of the restricted `N`-action.
Costs are absolute (unnormalized) unless stated otherwise. Cost is defined
for every p.m.p. countable relation, ergodic or not.

Inputs.

* (I1) Gaboriau's induction formula for complete sections, recorded as
  `fpbs-normalized-cost-induction-input`: if `A` is a complete section of an
  aperiodic p.m.p. relation `R` on `(Y,nu)`, then
  `C(R) - 1 = nu(A)(C_norm(R|_A) - 1)`, equivalently
  `C_abs(R|_A) = C(R) - nu(Y \ A)`.
* (I2) Marker lemma (Kechris--Miller, *Topics in orbit equivalence*,
  Lemma 6.7): an aperiodic countable Borel equivalence relation admits a
  decreasing sequence of Borel complete sections with empty intersection.
* (I3) Hulanicki--Reiter: the trivial representation of a countable group is
  weakly contained in its left regular representation iff the group is
  amenable.
* Burnside algebra, used only in Section 3: `B(m,n)` is relatively free in
  the variety of groups of exponent `n`; it is infinite for `m >= 2` and odd
  `n >= 665` (Adian); and for odd `n >= 665` the centralizer of every
  nontrivial element is cyclic of order `n` (Donoso-Echenique--Silva,
  arXiv:2608.20472, Lemma 2.4).

## 1. Theorem A: quotient-split actions have cost one

**Theorem A.** Let `N` be an infinite normal subgroup of `Gamma` with `Q`
infinite. Assume there is `K < infinity` such that every free p.m.p. action of
`N`, ergodic or not, has cost at most `K`. Let `alpha` be a free action of
`Gamma` on `(X,mu)` admitting a `Gamma`-equivariant factor map
`phi : X -> Y` onto a free p.m.p. action `sigma` of `Q` on `(Y,nu)` (with
`Gamma` acting on `Y` through `pi_Q`) of finite cost `C(sigma)`. Then
`C(alpha) = 1`.

*Proof.* Write `mu = integral mu_y d nu(y)` for the disintegration along `phi`.

(a) *Fibres.* `N` acts trivially on `Y` and preserves `mu`, so by uniqueness
of disintegration `mu_y` is `N`-invariant for `nu`-a.e. `y`. If `phi(x) = y`
and `phi(gamma x) = y`, then `pi_Q(gamma) y = y`, so `pi_Q(gamma) = e` by
freeness of `sigma`, i.e. `gamma in N`. Hence the `R_alpha`-class of `x`
meets `phi^(-1)(y)` in exactly the orbit `N x`.

(b) *Active set.* Fix `delta, eta, epsilon in (0,1)`. `Q` is infinite and
`sigma` is free, so `R_sigma` is aperiodic and has a Borel complete section
`A` with `nu(A) <= delta`. Put `B = phi^(-1)(A)`. Then `mu(B) = nu(A)`, `B` is
`N`-invariant, and `B` meets every `R_alpha`-class.

(c) *Graphing `Phi_1`.* The restriction of `alpha` to `N` on `B`, with
normalized measure, is a free p.m.p. action of `N`. By hypothesis
`R_alpha^N|_B` has a generating graphing of absolute cost at most
`(K+epsilon) mu(B) <= (K+epsilon) delta`.

(d) *Graphing `Phi_2`.* Enumerate `Gamma = {gamma_1, gamma_2, ...}`. For
`x` outside `B` let `k(x)` be the least `k` with `gamma_k x in B`, which
exists by (b). With `D_k = {x not in B : k(x) = k}`, let `Phi_2` consist of
the partial maps `gamma_k|_(D_k)`. Its cost is `mu(X \ B) <= 1`.

(e) *Graphing `Phi_3`.* By (I1) the relation `R_sigma|_A` has absolute cost
`C(sigma) - nu(Y \ A) <= C(sigma)`. Choose a generating graphing `Psi` of it
of cost at most `C(sigma) + epsilon`. Since `sigma` is free, each partial map
of `Psi` splits into countably many pieces on which it is the restriction of
a single group element; so we may assume `Psi` consists of maps
`q_j|_(E_j)` with `E_j` and `q_j E_j` contained in `A`, and
`sum_j nu(E_j) <= C(sigma) + epsilon`. Fix lifts `g_j in Gamma` of `q_j`.

The relation `R_alpha^N` is aperiodic because `N` is infinite and acts freely.
By (I2) take Borel complete sections `M_1 >= M_2 >= ...` of `R_alpha^N` with
empty intersection. For `nu`-a.e. `y` we have `mu_y(M_k) -> 0`; let `k(y)` be
the least `k` with `mu_y(M_k) <= eta`, a Borel function, and put
`S = {x in B : x in M_(k(phi(x)))}`. Every `M_k` meets every `N`-orbit, and
`N`-orbits lie inside fibres of `phi`, so `S` meets every `N`-orbit contained
in `B`, and `mu_y(S) <= eta` for a.e. `y in A`.

Let `Phi_3` consist of the partial maps `g_j` restricted to
`S intersect phi^(-1)(E_j)`. Its cost is

    sum_j integral_(E_j) mu_y(S) d nu(y)  <=  eta sum_j nu(E_j)  <=  eta (C(sigma) + epsilon).

(f) *Generation.* Let `x in X` and `gamma in Gamma`. Move `x` to `x' in B`
by at most one `Phi_2`-edge, and `gamma x` to `y' in B` likewise. The points
`a = phi(x')` and `a' = phi(y')` of `A` lie in one `R_sigma`-class, so there
is a `Psi`-path `a = a_0, a_1, ..., a_r = a'`. By (a) the `R_alpha`-class of
`x'` contains exactly one `N`-orbit `O_i` over each `a_i`, and `O_i` is
contained in `B`, so `Phi_1` connects all points of `O_i`. If
`a_(i+1) = q_j a_i` with `a_i in E_j`, pick `s in O_i intersect S`; then
`g_j s` lies over `a_(i+1)` in the same `R_alpha`-class, hence in `O_(i+1)`,
and `(s, g_j s)` is a `Phi_3`-edge. If instead `a_i = q_j a_(i+1)` with
`a_(i+1) in E_j`, use `s in O_(i+1) intersect S` and the edge `(s, g_j s)`.
Concatenating these pieces gives a path from `x` to `gamma x`. So
`Phi_1 union Phi_2 union Phi_3` generates `R_alpha`.

(g) *Cost.* `C(alpha) <= (K+epsilon) delta + 1 + eta (C(sigma) + epsilon)`.
Let `delta, eta, epsilon -> 0`. Every orbit is infinite, so `C(alpha) >= 1`. QED

**Corollary A.1 (group cost).** Under the hypotheses on `N` and `Q`, if `Q`
has a free action of finite cost (for instance `Q` finitely generated), then
for every free action `beta` of `Gamma` and every free finite-cost action
`sigma` of `Q`, the diagonal action `beta x sigma` has cost one. In particular
`cost(Gamma) = 1`. This is Gaboriau's normal subgroup theorem for the
infimal cost, which Donoso-Echenique--Silva quote as their Theorem 2.2 with
the weaker hypothesis `cost(N) < infinity`; the uniform hypothesis above is
what makes the per-action statement possible.

**Where the hypothesis holds.** If `N` is finitely generated, `K = d(N)`
works for every action. For every infinite subgroup of a large odd free
Burnside group, `K = c_n <= 2 - 2/n` works by `fpbs-burnside-common-upper-cost`.

## 2. Proposition B: quotient-split actions are not weakly contained in Bernoulli

**Proposition B.** Let `N` be a nonamenable normal subgroup of `Gamma` and let
`alpha` be a p.m.p. action of `Gamma` that has a nontrivial factor on which
`N` acts trivially; every quotient-split action with nontrivial `sigma` is
such an action. Then `alpha` is not weakly contained in the Bernoulli shift
`b_Gamma` on `[0,1]^Gamma`.

*Proof.* Pull back a unit vector of `L^2_0` of the factor; this gives a unit
vector `f in L^2_0(X,mu)` fixed by `N`.

First, `alpha weakly contained in b` implies that the Koopman representation
of `alpha` on `L^2_0` is weakly contained, in Zimmer's sense, in that of `b`.
For a simple function `u = sum_i c_i 1_(A_i)` the coefficient
`<kappa(g) u, u> = sum_(i,j) c_i conj(c_j) mu(g A_i intersect A_j)` involves
only finitely many numbers `mu(g A_i intersect A_j)`. Weak containment
supplies sets `A'_i` in the Bernoulli space reproducing these numbers, for
`g` in a prescribed finite set including `e`, within any tolerance; the means
are reproduced through `g = e`. Simple functions are dense, so every diagonal
coefficient of `kappa_alpha^0` is a limit, uniformly on finite sets, of
diagonal coefficients of `kappa_b^0`.

Second, `kappa_b^0` is a direct sum of quasi-regular representations
`l^2(Gamma/K)` with `K` finite. Choose an orthonormal basis `e_0 = 1, e_1,
e_2, ...` of `L^2[0,1]`. The finite tensor products
`prod_(h in F) e_(k(h))(x_h)`, with `F` a finite nonempty subset of `Gamma`
and every `k(h) >= 1`, form an orthonormal basis of `L^2_0([0,1]^Gamma)`.
`Gamma` permutes this basis, and the stabilizer of a basis vector lies inside
the setwise stabilizer of `F` under left translation, which is finite. Each
`l^2(Gamma/K)` with `K` finite is a subrepresentation of `lambda_Gamma`, and
`lambda_Gamma` restricted to `N` is a multiple of `lambda_N`.

Restricting the weak containment to `N`, the coefficient `n -> <kappa(n) f, f> = 1`
shows that the trivial representation of `N` is weakly contained in a
multiple of `lambda_N`, hence in `lambda_N`. By (I3), `N` is amenable, a
contradiction. QED

**What this rules out.** For finitely generated `Gamma` cost is monotone under
weak containment (the input behind `fpbs-bernoulli-maximal-cost`): a free
`a` weakly contained in `b_Gamma` has `C(a) >= C(b_Gamma)`. The tempting
upgrade of Theorem A to fixed price one would exhibit a cost-one
quotient-split action weakly contained in `b_Gamma`, giving `C(b_Gamma) = 1`
and then fixed price one by Abert--Weiss maximality. Proposition B kills that
upgrade whenever `N` is nonamenable. When `N` is infinite and amenable,
`Gamma` already has fixed price one by Gaboriau's criterion for weakly normal
subgroups of fixed price one (Gaboriau 2000, Critere VI.24), so Theorem A adds
nothing new there. This is the dead route
`fpbs-dead-split-cost-one-weak-containment-transfer`.

## 3. The open per-action statement and the Burnside consequence

**Open statement** (`fpbs-normal-subgroup-bounded-cost-fixed-price-one`). Let
`N` be an infinite normal subgroup of `Gamma` with `Q` infinite, and suppose
every free p.m.p. action of `N` has cost at most some `K < infinity`. Then
`Gamma` has fixed price one.

Known cases and status.

* Direct products `G x G'` of two infinite countable groups: fixed price one
  holds with no cost hypothesis at all, by Khezeli, *Products of infinite
  countable groups have fixed price one*, arXiv:2509.08325, Theorem 1.1,
  quoted from the arXiv html rendering: "The product of any two infinite
  countable groups has fixed price one." Bevilacqua--Bowen, arXiv:2510.05459,
  record that `Gamma x Gamma` was previously known only when `Gamma` has an
  infinite amenable subgroup, which shows this open statement is not
  classical even for finitely generated `N` with a complement commuting
  with it.
* Infinite amenable `N`: known (Section 2).
* Quotient-split actions: Theorem A.
* Under the hypothesis, the statement is equivalent, through
  `fpbs-factor-invariance-equals-fixed-price` and Theorem A, to cost
  preservation along the projections `alpha x sigma -> alpha` for free
  `Gamma`-actions `alpha` and free finite-cost `Q`-actions `sigma`. That
  restates the statement; it does not reduce it, and it is not recorded as a
  route.

**Lemma 3.1 (Burnside normal closure).** Let `m >= 3`, let `n >= 665` be odd,
let `G = B(m,n)` with free generators `x_1, ..., x_m`, and let `N` be the
normal closure of `x_1`. Then `N` is infinite, `H = <x_2, ..., x_m>` is
isomorphic to `B(m-1,n)`, `G = N semidirect H`, and `G/N` is isomorphic to
`B(m-1,n)`, which is infinite.

*Proof.* Let `y_1, ..., y_(m-1)` generate `B(m-1,n)` freely. Relative freeness
gives homomorphisms `theta : B(m-1,n) -> G` with `y_i -> x_(i+1)`, and
`r : G -> B(m-1,n)` with `x_1 -> e` and `x_i -> y_(i-1)` for `i >= 2`. Then
`r theta` is the identity, so `theta` is injective and `H = theta(B(m-1,n))`
is isomorphic to `B(m-1,n)`. Since `x_1` is in the kernel of `r`, `N` is too,
and `r` induces `rbar : G/N -> B(m-1,n)`. The map
`thetabar : B(m-1,n) -> G/N` induced by `theta` is onto, because `G/N` is
generated by the images of `x_2, ..., x_m`. From `rbar thetabar = id`,
`thetabar` is an isomorphism, so `ker r = N`. Also `H intersect N = {e}`
because `r theta = id`, and `HN = G`; so `G = N semidirect H`. The group
`B(m-1,n)` is infinite because `m - 1 >= 2` and `n >= 665` is odd.

If `N` were finite, conjugation would give a homomorphism from `G` to the
finite group `Aut(N)`. Its kernel `C_G(N)` would have finite index in the
infinite group `G`, so it would be infinite, while `C_G(N)` is contained in
`C_G(x_1)`, which has order `n`. So `N` is infinite. QED

**Consequence 3.2.** Assume the open statement. For odd `n` in the range of
`fpbs-burnside-common-upper-cost` (and `n >= 665`), let `m >= 3`,
`G = B(m,n)`, and let `N` be as in Lemma 3.1. By the common-upper-cost
theorem, every free action of the infinite subgroup `N` has cost at most
`c_n <= 2 - 2/n`, so the hypothesis holds with `K = 2`, and `G` has fixed
price one. Hence `C*(B(m,n)) = 1`. The same theorem gives
`c_n = C*(B(m,n))`, so `c_n = 1`: every infinite subgroup of every `B(m',n)`,
including `B(2,n)`, has upper cost one. This is `fpbs-burnside-upper-cost-one`.
Through `fpbs-burnside-explicit-action-pair` it closes the Burnside
counterexample branch in the negative direction, since
`fpbs-burnside-positive-upper-cost` asks for `c_n > 1`. The route is
`fpbs-burnside-upper-cost-one-via-normal-closure`.

## 4. Where the obvious attacks on the open statement die

* **Transfer Theorem A to the Bernoulli shift.** Dead for nonamenable `N` by
  Proposition B.
* **Select whole `N`-orbits sparsely, as in Theorem A, inside an arbitrary
  action.** An `N`-invariant set of small positive measure is exactly what
  Theorem A uses. It does not exist when the restriction of `alpha` to `N` is
  ergodic, which is the case for the Bernoulli shift of `Gamma` restricted to
  any infinite `N`. This is the vertical-constancy obstacle that Khezeli's
  product theorem gets around with horoball processes built as weak limits of
  factors of i.i.d.
* **Adapt Khezeli's horoballs to extensions.** That construction uses the
  product structure: a left-invariant weighted product metric and two
  commuting infinite directions. In a split extension `N semidirect H` the
  complement `H` exists but does not commute with `N`. Whether an analogue
  exists is open, and it is not attempted here.
* **Slutsky's product-neighbourhood criterion** (arXiv:2607.20273,
  Theorem 1.1, `inf |F S F^(-1)| / |F|^2 = 0`). It yields fixed price one
  directly where it applies. Donoso-Echenique--Silva note that verifying it
  for free Burnside groups "may be challenging" because of Coulon--Steenbock
  product-set growth. Not examined further here.

## 5. A quantitative floor for ergodic percolation on Kazhdan groups

This section concerns `fpbs-kazhdan-sparse-spines`, not the normal subgroup
statement. It records why the Hutchcroft--Pete recursion cannot be run
entirely inside the class of factors of i.i.d.

**Proposition D.** Let `Gamma` have a Kazhdan pair `(S, kappa)`: `S` is
finite and symmetric, and every unitary representation `pi` without nonzero
invariant vectors satisfies `max_(s in S) ||pi(s) v - v|| >= kappa ||v||` for
all `v`. Let `mu` be an ergodic `Gamma`-invariant probability measure on
`{0,1}^Gamma`, with the shift `(g omega)(h) = omega(g^(-1) h)`, and put
`p = mu(omega(e) = 1)`. Then

    max_(s in S) mu(omega(s) != omega(e))  >=  kappa^2 p (1 - p).

*Proof.* The Koopman representation on `L^2_0(mu)` has no invariant vectors
because `mu` is ergodic. The function `f = 1_(omega(e)=1) - p` lies in
`L^2_0(mu)` with `||f||^2 = p(1-p)`, and `(pi(s) f)(omega) = f(s^(-1) omega) =
1_(omega(s)=1) - p`. So `||pi(s) f - f||^2 = mu(omega(s) != omega(e))`, and
the Kazhdan inequality gives the claim. QED

Every finite generating set of a Kazhdan group is a Kazhdan set for some
`kappa > 0`, so the floor applies to site percolation on every Cayley graph.

**Consequence.** Hutchcroft--Pete, arXiv:1810.11015, Proposition 2.2, build
invariant percolations `mu_i` with marginal `p` whose adjacent disagreement
tends to zero, converging weakly to `p delta_V + (1-p) delta_empty`. By
Proposition D this convergence is impossible inside the ergodic class, and
every factor of i.i.d. is ergodic. So a proof that keeps every stage a factor
of i.i.d. can never approach the non-ergodic limit and cannot invoke the
Glasner--Weiss closedness of ergodic measures through it. Within that class,
the most the limit argument yields is that the exact thinning of clusters
must fail at some stage, which is where infinite clusters appear. It supplies
no positive-frequency cluster, and no sparse factor-of-i.i.d. spine. An
admissible version of the strategy needs a quantitative condensation
statement at disagreement at least `kappa^2 p (1-p)`, which Hutchcroft--Pete
do not provide. This is the dead route
`fpbs-dead-fiid-hutchcroft-pete-limit-recursion`.

## 6. Sources read for this note

* Hutchcroft--Pete, arXiv:1810.11015v2, pages 1--6 from the PDF: the abstract
  ("It remains open if they have fixed price 1"), Proposition 2.1, and the
  remark that their construction is far from a factor of i.i.d.
* Donoso-Echenique--Silva, arXiv:2608.20472, html rendering: Theorem 1.2,
  Theorem 2.2 (Gaboriau's normal subgroup theorem for infimal cost), Lemma 2.4
  (cyclic centralizers of order `n`), Proposition 2.7, and the remark on
  Slutsky's criterion.
* Khezeli, arXiv:2509.08325, html rendering: Theorem 1.1.
* Slutsky, arXiv:2607.20273, html rendering: Theorem 1.1.
* Bevilacqua--Bowen, arXiv:2510.05459, html rendering: the remark on
  `Gamma x Gamma`.
* arXiv:2307.11728, html rendering: the statement of Gaboriau's criterion for
  weakly normal subgroups.

The html renderings were read through a summarizing fetch tool, so only
theorem statements are relied on above. No proof step of the cited papers
has been independently re-checked.
