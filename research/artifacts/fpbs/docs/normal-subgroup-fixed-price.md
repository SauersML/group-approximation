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

## 6. Audit: fixed-price-one criteria and closed hyperbolic 3-manifold groups

Here `M` is a closed hyperbolic 3-manifold and `Gamma = pi_1(M)`, a
torsion-free cocompact lattice in `PSL(2,C)` and a non-elementary hyperbolic
group. By virtual fibering `Gamma` has a finite-index subgroup
`N semidirect Z` with `N` a closed surface group, and fixed price one passes
from that subgroup to `Gamma` (`fpbs-fibered-3-manifold-cost-inputs`). This
section records which fixed-price-one criteria are theorems, with hypotheses
as the sources state them, and why each one misses `Gamma`. Quotations were
checked against the PDFs listed in Section 7. The proofs of the cited results
were not re-checked.

### 6.1 Criteria that are theorems

**Gaboriau, lecture notes** "Around the orbit equivalence theory, measure
equivalence, cost and l^2 Betti numbers" (October 3, 2025), Sections 2.5--2.7.

* Theorem 2.45: if `Gamma` is the increasing union of subgroups `Gamma_n` with
  `Gamma_(n+1) = <Gamma_n, gamma_(n+1)>` and
  `gamma_(n+1)^(-1) Gamma_n gamma_(n+1) intersect Gamma_n` infinite, then
  `C(R_Gamma) <= C(R_(Gamma_0))`. Corollary 2.46: a graph of groups whose
  vertex groups have fixed price one and whose edge groups are infinite has
  fixed price one.
* Corollary 2.48 (Infinite normal subgroup), verbatim: "If Λ ◁ Γ is an
  infinite normal subgroup, then for every free p.m.p. action Γ↷α(X,μ):
  C(R_{Γ↷αX}) ≤ C(R_{Λ↷αX})." Corollary 2.49 gives the same inequality for
  commensurated subgroups.
* Corollary 2.52: fixed price one when `Gamma` is a direct product of infinite
  groups one of which contains a fixed-price-one subgroup, when `Gamma` is
  generated by two commuting infinite subgroups one of which contains a
  fixed-price-one subgroup, or when the center contains a fixed-price-one
  subgroup. Page 21: "Fixed price 1 for all direct product of infinite groups
  ... has been announced by Khezeli [Khe25]."
* Theorem 2.54, verbatim: "Let Γ be a lattice in a semi-simple connected Lie
  group with real rank ≥ 2. If Γ is non-cocompact or if Γ is reducible, then Γ
  has fixed price = 1."
* Theorem 2.56 (Finite cost normal subgroup [Gab02b, Th. 3.4]), verbatim: "If
  1 → Λ → Γ → Q → 1 is an exact sequence of infinite groups, and C_*(Λ) < ∞,
  then C_*(Γ) = 1. If Γ is moreover non-amenable, then Γ is non treeable."
  This concerns infimal cost only.
* 2.30: the closed surface group of genus `g` has fixed price `2g - 1`.

**Gaboriau, "Coût des relations d'équivalence et des groupes"**, Invent. Math.
139 (2000), Critère VI.24(2), verbatim: "si Λ est un sous-groupe distingué
infini à prix fixe de Γ, alors C(Γ) ≤ C(Λ)". Slutsky cites VI.24(3) as the
weak normality criterion.

**Slutsky**, arXiv:2607.20273v1.

* Theorem 1.1, verbatim: "Let Γ be a discrete, finitely generated group, and
  let S be a finite symmetric generating set with e ∈ S. Suppose that there
  are finite sets Fₙ ⊆ Γ, with e ∈ Fₙ, such that |FₙSFₙ⁻¹|/|Fₙ|² → 0. Then Γ
  has fixed price one."
* Corollary 1.2, verbatim: "Let Γ be a finitely generated group. Suppose that
  Γ contains an infinite amenable subgroup Λ such that Λ ∩ s⁻¹Λs is infinite
  for every s ∈ S. Then Γ has fixed price one." Corollary 2.5 is the version
  with finite subgroups `K_n` and `min_s |K_n intersect s K_n s^(-1)| -> infinity`.
* Theorem 1.3 is the analogue for lcsc groups `G` with Haar measure `lambda`,
  and gives fixed price one for `G` and every lattice in `G`. Corollary 1.4,
  verbatim: "Let G admit a proper left-invariant metric with D = max_{s∈S}
  d(e,s) and such that liminf_{R→∞} λ(B(2R+D))/λ(B(R))² = 0, then G has fixed
  price one, and so does every lattice in G." The remark after it says the
  hypothesis holds whenever `lambda(B(R))` is comparable to `e^(hR) R^a` with
  `a > 0`.
* Corollaries 1.5--1.7 and 2.4: real rank at least two, affine buildings of
  rank at least two, products `G_1 x G_2`, and `G x H` for finitely generated
  infinite `G` and `H`. Corollary 1.8: every group these criteria cover has
  `beta_1^(2) = 0` and vanishing rank gradient along every Farber sequence.

**Bevilacqua--Bowen**, arXiv:2510.05459.

* Theorem 8.1, verbatim: "If Γ has an imp action which is limit-amenable,
  partially doubly recurrent, and has normalized cost p then Γ has max-cost at
  most p. In particular, if p = 1 then Γ has fixed price 1." Its proof goes
  through Theorem 7.1, which also asks that a.e. ergodic component be
  infinite, non-atomic and essentially free.
* Theorem 4.12: if `Gamma` is exact, every limit-amenable action is amenable.
  The proof of Corollary 9.4 adds that amenable imp actions have normalized
  cost one. An amenable imp action is limit-amenable, since the definition
  asks only for approximation by amenable imp actions, as the proof of Lemma
  4.8 uses it. So for exact `Gamma`, Theorem 8.1 turns a single amenable,
  partially doubly recurrent imp action into fixed price one.
* Definitions 27 and 40 (PDR), verbatim: "Let Γ↷(X,μ) be an ergodic imp
  action. By Theorem A.1, X² is the disjoint union of Γ-invariant measurable
  sets Con(X²) and Dis(X²) and the restriction of Γ to Con(X²) is infinitely
  conservative. We will say the action Γ↷(X,μ) is partially doubly recurrent
  (PDR) if for a.e. x,y ∈ X there exist x = x₁, x₂, ..., xₙ = y with
  (xᵢ,xᵢ₊₁) ∈ Con(X²) for all i." By Definitions 37 and 39, `Dis(Y)` is the
  union of the ergodic components of `Y` that are atomic orbits with finite
  stabilizers, and `Con(Y)` is its complement. Both come from the ergodic
  decomposition, so they are defined up to null sets. By Theorem A.1 and
  Definition 38, every subset of `Con(Y)` of positive measure has infinitely
  many return times at almost every point.
* Theorem 9.3 builds a limit-amenable doubly recurrent imp action on
  `H(Gamma) = H_0 + Z` (Definition 31), where `H_0` is the closure of the
  functions `d(x, .) - |x|` in `Lip(Gamma)`. The input is a left-invariant,
  proper, approximately sub-additive integer-valued quasi-metric `d` on a
  non-amenable group, with the overlapping neighbourhoods property (ONP,
  Definition 30). Corollary 9.4, verbatim: "If (Γ,d) has the overlapping
  neighborhoods property and Γ is exact then Γ has fixed price 1."
* Corollaries 10.8 and 10.9: `Gamma x Gamma`, and products of two groups of
  exact polynomial-exponential growth. Remark 21 lists "hyperbolic groups with
  respect to word metrics [Coo93]" among the groups with that growth.

**Abert--Nikolov**, arXiv:math/0701361v3. Theorem 1 identifies the rank
gradient of a Farber chain with cost minus one. Theorem 2, verbatim: "Either
the Rank vs Heegaard genus conjecture is false or the Fixed price problem has
a negative solution."

### 6.2 Why each criterion misses `pi_1(M)`

* **Normal and commensurated subgroups** (Gaboriau 2000 VI.24(2), notes 2.48
  and 2.49). These bound the cost of `Gamma` by the cost of the subgroup. The
  fibre group `N` has fixed price `2g - 1 >= 3`, so the bound is `2g - 1`.
  Infinitely generated normal or commensurated subgroups were not analysed.
* **Chains and amenable subgroups** (notes 2.45 and 2.46, Gaboriau 2000
  VI.24(3), Slutsky 1.2 and 2.5). A starting subgroup of fixed price one, or
  an infinite amenable one, must reach all of `Gamma` through infinite
  intersections, or finite subgroups must grow along the generators. In
  `Gamma` the infinite amenable subgroups are cyclic and there are no
  nontrivial finite subgroups. If `<g> intersect gamma <g> gamma^(-1)` is
  infinite, then `gamma` lies in the maximal cyclic subgroup containing `g`,
  so every chain from a cyclic subgroup stays cyclic. Starting from `N` gives
  the bound `2g - 1` again.
* **Products, commuting subgroups, center** (notes 2.52, Khezeli,
  Bevilacqua--Bowen 10.8 and 10.9, Slutsky 1.7 and 2.4). `Gamma` has trivial
  center and cyclic centralizers of nontrivial elements. So two commuting
  infinite subgroups lie in one cyclic subgroup, and `Gamma` contains no
  product of two infinite groups.
* **Higher rank** (notes 2.54, Slutsky 1.5 and 1.6). `PSL(2,C)` has real rank
  one, and `Gamma` is cocompact and irreducible.
* **Infimal cost** (notes 2.56). The fibration gives `C_*(Gamma) = 1`, which is
  how the root claim records infimal cost one. It does not give cost one for
  every free action.
* **Ball growth** (Slutsky 1.4). Balls in `H^3`, in `PSL(2,C)` with a
  left-invariant Riemannian metric making `PSL(2,C) -> H^3` a Riemannian
  submersion, and word balls in `Gamma` all grow like `e^(hR)` with no
  polynomial factor. So `lambda(B(2R+D)) / lambda(B(R))^2` stays bounded below
  (Remark H).
* **ONP** (Bevilacqua--Bowen 9.4). ONP fails for every word metric on a
  non-elementary hyperbolic group (Proposition G). Other metrics in the class
  of Theorem 9.3 were not examined.
* **Theorem 8.1 through natural actions.** `Gamma` is exact, so this route
  needs an amenable PDR imp action. The actions on horospheres and on
  geodesics of `H^3` are amenable, ergodic, essentially free and non-atomic,
  and neither is PDR. For a word metric, no ergodic invariant measure on
  `H(Gamma)` is PDR (Proposition F).
* **Slutsky's Theorem 1.1 with other sets.** Not settled. Balls fail
  (Remark H). If `F` lies in a maximal cyclic subgroup `C` and `s` in `S`
  lies outside `C`, then `|F s F^(-1)| = |F|^2`: from `a s b^(-1) = a' s
  b'^(-1)`, the element `a'^(-1) a` lies in `C intersect s C s^(-1)`, which is
  trivial. So a working sequence must be far from cyclic. None exists for
  `F_2` or surface groups, since they have fixed price above one.
  Product-set growth estimates in hyperbolic groups (Delzant--Steenbock) are
  the natural tool, and they were not read.

### 6.3 The bounded-cost statement in this light

* Under its hypothesis `C_*(N) <= K`, so notes 2.56 already give
  `C_*(Gamma) = 1`. So `fpbs-normal-subgroup-bounded-cost-fixed-price-one` is
  exactly the fixed price question for this class of extensions. By
  Abert--Nikolov Theorem 1, its conclusion gives vanishing rank gradient along
  Farber chains of `Gamma`.
* Test cases.
  - `(Z/2) wr Z` with `N` the base group: amenable, so fixed price one
    (Gaboriau 2000, abstract: "The cost of every infinite amenable group
    equals 1").
  - `N = [F_2, F_2]` in `F_2`: `N` is free of infinite rank, so its free
    actions have unbounded cost and the hypothesis fails, while `F_2` has
    fixed price 2. So the cost hypothesis cannot be dropped.
  - A closed surface group: its infinite normal subgroups of infinite index
    are free of infinite rank (standard), so the hypothesis fails, which is
    consistent with fixed price `2g - 1`.
  - Direct products `G x G'`: Khezeli, with no cost hypothesis.
  - Finitely generated `N`: the hypothesis holds with `K = d(N)`.
* **Theorem 8.1 read backwards for surface groups.** Closed surface groups are
  exact and have fixed price above one. So none of their amenable imp actions
  whose ergodic components are infinite, non-atomic and essentially free is
  PDR, including their actions on horocycles and on geodesics of `H^2`. Any
  PDR action of `pi_1(M)` has to use structure that surface groups lack. For
  `H^2`, Proposition F is forced; for `H^3` it has to be proved.

### 6.4 The natural amenable actions are not PDR, and ONP fails

**Lemma E (no conservative part).** Let `Gamma` act on a standard Borel space
`Y`, preserving a σ-finite measure `nu`. Let `Y_0` be an invariant Borel set
and `Phi : Y_0 -> P` a Borel `Gamma`-equivariant map to a Borel `Gamma`-space
`P = union_j K_j`, where each `K_j` is Borel and
`{gamma : gamma K_j intersect K_j nonempty}` is finite. Then
`Con(Y) intersect Y_0` is null. If `Y = X^2` and `nu = mu x mu` for an imp
action `Gamma ↷ (X, mu)`, and `Y_0` is conull, then the action on `X` is not
DR. If moreover the action on `X` is ergodic and the off-diagonal part of
`X^2` has positive measure, then it is not PDR.

*Proof.* If `Con(Y) intersect Y_0` had positive measure, so would
`Z = Con(Y) intersect Phi^(-1)(K_j)` for some `j`. By Theorem A.1, almost
every `z` in `Z` has infinitely many `gamma` with `gamma z` in `Z`. Each such
`gamma` has `Phi(z)` and `gamma Phi(z) = Phi(gamma z)` in `K_j`, so it lies in
a finite set, a contradiction. When `Y_0` is conull, `Dis(X^2)` is conull. By
the second part of Theorem A.1, a subset of finite positive measure then has
finitely many returns at almost every point, so the diagonal action is not
infinitely conservative. For PDR, take the representative
`Con(X^2) = empty`. Then a chain as in Definition 40 joins `x` only to itself,
and the diagonal is not conull. QED

**How Definition 40 is read.** The definition is written pointwise, but
`Con(X^2)` comes from the ergodic decomposition and is defined only up to
null sets. Lemma E reads PDR as unchanged by null modifications of
`Con(X^2)`, and the pointwise reading with an arbitrary representative cannot
be what is meant. Take a closed surface group acting on the oriented geodesics
of `H^2`. This action is ergodic, amenable, essentially free and non-atomic.
The invariant null set of pairs of geodesics sharing an endpoint joins any
`(a,b)` to `(c,d)` through `(a,d)`. Adding that set to `Con(X^2)` would make
the action PDR, and Theorem 8.1 would give fixed price one instead of
`2g - 1`.

**Proposition F.** Let `Gamma = pi_1(M)` and `G = PSL(2,C)`.

(a) The action of `Gamma` on the space `G/MN` of horospheres of `H^3`, with
its `G`-invariant measure, is ergodic, amenable, free and non-atomic, and it
is neither DR nor PDR.

(b) The same holds for the space `G/MA` of oriented geodesics of `H^3`,
except that the action is essentially free rather than free.

(c) Let `Gamma` be a torsion-free non-elementary hyperbolic group with a word
metric `d`, and `mu` a `Gamma`-invariant σ-finite measure on `H(Gamma)`. Then
`Con(H(Gamma)^2)` is `mu x mu`-null, and `(H(Gamma), mu)` is neither DR nor
PDR.

Ergodicity (Moore's theorem, since `MN` and `MA` are non-compact),
amenability (Zimmer, since `MN` and `MA` are amenable) and freeness (`Gamma`
has no parabolic or elliptic elements, and has countably many axes) are
standard and were not re-read.

*Proof of (a).* For a fixed centre the horospheres form a null set, so pairs
with distinct centres `xi_1 != xi_2` are conull. For such a pair let
`Phi(h_1, h_2)` be the midpoint of the segment of the geodesic `(xi_1 xi_2)`
between the points where it crosses `h_1` and `h_2`. This is continuous and
`G`-equivariant. `Gamma` acts properly discontinuously on `P = H^3`, the union
of the closed balls about a base point, so Lemma E applies. QED

*Proof of (b).* Pairs of geodesics with four distinct endpoints are conull.
Such a pair either meets in one point, which is `Phi`, or has a unique common
perpendicular, whose midpoint is `Phi`. Lemma E applies as in (a). QED

*Proof of (c).* Write `|g| = d(e,g)` and `(x.y)_w = (d(w,x) + d(w,y) -
d(x,y))/2`, and fix `delta` with
`(x.y)_w >= min((x.z)_w, (z.y)_w) - delta` for all `x, y, z, w`. Every `h` in
`H(Gamma)` has the form `h = r + lim_n (d(x_n, .) - |x_n|)`, with `r = h(e)`.

*Step 1.* Suppose `h_1 = r_1 + lim (d(x_n, .) - |x_n|)`,
`h_2 = r_2 + lim (d(y_n, .) - |y_n|)`, and `(x_n . y_n)_e <= K` for all `n`.
Then `max(h_1, h_2)(g) >= |g| - 2K - 2 delta + min(r_1, r_2)`. Indeed, put
`a_n = d(g, x_n) - |x_n|` and `b_n = d(g, y_n) - |y_n|`. Then
`(x_n . e)_g = (a_n + |g|)/2` and `(e . y_n)_g = (b_n + |g|)/2`, and
`d(x_n, y_n) >= |x_n| + |y_n| - 2K` gives `(x_n . y_n)_g <= (a_n + b_n + 2K)/2`.
The four-point condition at `g` gives
`a_n + b_n + 2K >= min(a_n, b_n) + |g| - 2 delta`, so
`max(a_n, b_n) >= |g| - 2K - 2 delta`. Now let `n -> infinity`.

*Step 2 (centres).* If `x_n` leaves every finite set, pick `g_t` at distance
`t` from `e` on a geodesic `[e, x_n]` and pass to a diagonal subsequence. This
gives `h(g_t) = r - t`, so `h` is unbounded below. Otherwise `h` is
`r + d(x, .) - |x|` for some `x`. If two sequences representing one unbounded
`h` converged to distinct points of `∂Gamma`, Step 1 with `h_1 = h_2 = h`
would give `h(g) >= |g| - const`. So each boundary `h` has a centre `c(h)` in
`∂Gamma`, every representing sequence converges to it, and
`c(gamma h) = gamma c(h)`.

*Step 3.* Let `Y_0` be the invariant set of pairs in which some coordinate
has the form `r + d(x, .) - |x|`, or both are boundary points with distinct
centres. Step 1 applies to these pairs, possibly after dropping finitely many
terms, so `max(h_1, h_2)` is integer-valued and tends to infinity. So
`Phi = argmin max(h_1, h_2)` is a finite nonempty subset of `Gamma`, and it is
equivariant because `(gamma h)(x) = h(gamma^(-1) x)`. Take `P` the finite
subsets of `Gamma` and `K_j` those inside `B(j)`. Then `gamma K_j` meets `K_j`
only if `gamma` is in `B(2j)`, and Lemma E gives `Con intersect Y_0` null.

*Step 4 (equal centres).* The rest of `H(Gamma)^2` is the set `D` of boundary
pairs with `c(h_1) = c(h_2)`. By Fubini and σ-finiteness, `D` is covered up to
a null set by the countably many `c^(-1)(xi)^2` with `mu(c^(-1)(xi)) > 0`.
Suppose `Con` meets one of them, `c^(-1)(xi_0)^2`, in positive measure. Then
for some `k` the set `Z` of those pairs with `|h_1(e)| <= k` also has positive
measure. A return `gamma` of `(h_1, h_2)` to `Z` fixes `xi_0` and has
`|h_1(gamma^(-1))| <= k`, since `(gamma h_1)(e) = h_1(gamma^(-1))`. The
stabilizer of `xi_0` is trivial or generated by a loxodromic `u` with fixed
points `xi_0` and `xi'` (standard). Say `u^n -> xi_0` as `n -> +infinity`.
Write `h_1(g) = r + |g| - 2 lim_m (x_m . g)_e` with `x_m -> xi_0`.

- As `n -> -infinity`, `u^n -> xi' != xi_0`, so the products `(x_m . u^n)_e`
  stay bounded for large `m`. So `h_1(u^n) -> +infinity`.
- As `n -> +infinity`: by the Morse lemma `u^0, ..., u^N` lie within `D_u` of
  a geodesic `[e, u^N]`, so `(u^N . u^n)_e >= |u^n| - D_u` for
  `0 <= n <= N`. For `N` and then `m` large, `(x_m . u^N)_e >= |u^n|`, and
  the four-point condition gives `(x_m . u^n)_e >= |u^n| - D_u - delta`. So
  `h_1(u^n) <= r - |u^n| + 2 D_u + 2 delta -> -infinity`.

So only finitely many `gamma` return, against Theorem A.1. So `Con` is null.
Not DR and not PDR then follow as in Lemma E, applied to each ergodic
component, through Lemma A.3. Ergodic components are infinite, because
`Gamma` fixes no point of `H(Gamma)`. QED

**Proposition G (ONP fails).** Let `Gamma` be a non-elementary hyperbolic
group with a word metric `d`. Then `(Gamma, d)` does not have the overlapping
neighbourhoods property of Bevilacqua--Bowen Definition 30.

*Proof.* By Coornaert, through Remark 21, there are `alpha > 0` and
`C_0 >= 1` with `C_0^(-1) e^(alpha n) <= |B(n)| <= C_0 e^(alpha n)`. A
polynomial factor would change nothing below. Fix `C > 0`, and call `(x, y)`
in `B(n)^2` good if `|x|, |y| >= n - L` and `(x.y)_e <= K`.

Let `(x, y)` be good and `z` in `B(x, n+C) intersect B(y, n+C)`. Then
`(x.z)_e >= (|z| - L - C)/2`, and likewise for `y`, so
`K >= (x.y)_e >= (|z| - L - C)/2 - delta`. That is,
`|z| <= R_0 = C + L + 2K + 2 delta`. So good pairs have
`|B(r) intersect B(x, n+C) intersect B(y, n+C)| <= |B(R_0)|` for all `r` and
`n`.

Bad pairs are rare.

- The fraction of `x` in `B(n)` with `|x| < n - L` is at most
  `C_0^2 e^(-alpha L)`.
- Fix `x`. If `(x.y)_e >= K`, then `|x| >= K`. Let `x_K` and `y_K` be the
  points at distance `K` from `e` on geodesics `[e, x]` and `[e, y]`; they are
  `4 delta`-close (thin triangles, standard). So `y` lies in
  `x_K B(4 delta) B(n - K)`, which is at most a fraction
  `C_0^2 |B(4 delta)| e^(-alpha K)` of `B(n)`.

Choose `L` and `K` so that
`2 C_0^2 e^(-alpha L) + C_0^2 |B(4 delta)| e^(-alpha K) <= 1/2`. Then at least
half of `B(n)^2` is good for every `n`. With `m = |B(R_0)| + 1`, the quantity
in Definition 30 is at least `1/2` for every `r`. Since `C` was arbitrary, ONP
fails. QED

**Remark H (ball growth).** A ball of radius `R` in `H^3` has volume
`pi (sinh(2R) - 2R)`, comparable to `e^(2R)`. Take a left-invariant Riemannian
metric on `G = PSL(2,C)` making `G -> H^3 = G/K` a Riemannian submersion, and
let `c` be the diameter of `K`. Then the preimage of `B_(H^3)(R - c)` lies in
`B_G(R)`, which lies in the preimage of `B_(H^3)(R)`. So Haar measure of
`B_G(R)` is comparable to `e^(2R)` too. Word balls in `Gamma` are comparable
to `e^(alpha R)` (Coornaert). In each case `lambda(B(2R+D)) / lambda(B(R))^2`
is bounded below by a positive constant, so Slutsky's Corollary 1.4 does not
apply with these metrics. Other proper left-invariant metrics were not
examined.

## 7. Sources read for this note

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
