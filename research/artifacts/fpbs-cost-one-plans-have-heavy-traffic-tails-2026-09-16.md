# Near-cost-one routing plans carry heavy repeated traffic

September 16, 2026. A written deduction in the routing formalism of
`research/artifacts/fpbs/docs/fixed-price-conditional-traffic.md`, Section 2.
It answers one scope question recorded on
`fpbs-correlated-reuse-flags-removable`: whether the fixed-cutoff
uniform-integrability form of `fpbs-binary-entropy-traffic-tail-bound` could
follow from cost preservation. It cannot. Over a source action of cost one of
a nonamenable group, no source-near-optimal plan sequence has uniformly
integrable repeated traffic, while for groups with fixed price one cost is
preserved anyway. Nothing here proves or refutes cost preservation, the
target claim, or Fixed Price. No priority is claimed: the mechanism is a
flow-cut congestion count, and the finite-cell step is the standard marker
construction.

## 1. Setting and notation

Let Gamma be finitely generated and S a finite generating set, not
necessarily symmetric. Use right notation y -> yg. Let (Y,nu) carry a free
p.m.p. action of Gamma, with invariant null sets removed so that freeness
holds pointwise. A finite routing plan D is as in the conditional-traffic
artifact, Section 2:

* finitely many edge copies phi_j = T_{g_j}|A_j with arbitrary labels
  g_j in Gamma, repetitions allowed;
* for each s in S a measurable set E_s and, for y in E_s, a measurable
  chosen Phi-path tau_s(y) from y to ys, of length at most one finite L, where
  a hop may traverse a copy in either direction;
* the traffic k_j(z), counting occurrences of the copy (j,z) on chosen routes,
  identified by its forward starting point z in A_j;
* U_j = {k_j > 0}, r(D) = sum_s nu(Y minus E_s), B(D) = sum_j nu(U_j) + r(D).

The change-of-variables identity (2.3) of that artifact states, for
nonnegative measurable f_j,

    sum_j integral k_j f_j dnu = sum_s integral_{E_s} sum_{occurrences (j,z) in tau_s(y)} f_j(z) dnu(y).   (1.1)

For real T >= 0 put

    Q_j = (k_j - 1)_+,        Tail_T(D) = sum_j integral Q_j 1_{Q_j > T} dnu.

This is the tail quantity of `fpbs-binary-entropy-traffic-tail-bound`, there
used with T >= 1; here any T >= 0 is allowed. The measure of a measurable set
P of edge copies is m(P) = sum_j nu({z in A_j : (j,z) in P}).

The right edge Cheeger constant of (Gamma,S) is

    h_S = inf { |{(g,s) in F x S : gs not in F}| / |F| : F finite, nonempty }.   (1.2)

It is positive if and only if Gamma is nonamenable. Indeed
|{g in F : gs not in F}| = |Fs minus F| = |Fs symmetric-difference F|/2. If
h_S = 0 there are finite sets F with |Fs sym-diff F| < eps |F| for all s in
S, and the triangle inequality |F gs sym-diff F| <= |F g sym-diff F| +
|F s sym-diff F|, together with |F s^{-1} sym-diff F| = |F sym-diff Fs|,
gives |Fg sym-diff F| <= |g|_S eps |F| for every g, a right Folner sequence.
Conversely a right Folner sequence makes the ratio in (1.2) tend to zero.

## 2. The theorem

**Theorem 1.** Let Gamma be infinite. For every finite routing plan D for S
on a free p.m.p. action of Gamma and every real T >= 0,

    h_S <= (T+1) (B(D) - 1) + Tail_T(D).                              (2.1)

**Corollary 2.** Assume Gamma is nonamenable.

(a) If every traffic value is at most M, where M >= 1, then
B(D) >= 1 + h_S/M. In particular B(D) > 1 for every finite plan.

(b) If B(D_n) -> 1, then liminf_n Tail_T(D_n) >= h_S for every T >= 0. Hence
lim_{T -> infinity} sup_n Tail_T(D_n) = 0 fails, and so does
Tail_{T}(D_n) -> 0 for any fixed T.

(c) If eps = B(D) - 1 lies in (0, h_S], then
sum_j integral Q_j^2 dnu >= (h_S - eps)^2 / (4 eps).

(d) If B(D_n) -> 1 and real cutoffs T_n >= 0 satisfy Tail_{T_n}(D_n) -> 0,
then T_n >= h_S / (4 (B(D_n) - 1)) for all large n. If moreover
T_n H_n -> 0 for nonnegative numbers H_n, then H_n / (B(D_n) - 1) -> 0.

Theorem 1 needs Gamma infinite. For a finite group h_S = 0 but plans with
B < 1 exist, for instance Z/2 with a half-space edge traversed in both
directions. For infinite amenable Gamma the proof below still gives B(D) >= 1,
so (2.1) holds with h_S = 0. The content is the nonamenable case.

**Corollary 3 (strictness).** Let Gamma = F_2 x Z with S the union of free
generators and the central generator. Every free factor map pi: Y -> X of
free p.m.p. actions of Gamma has C(X) = C(Y) = 1 and admits plans D_n on Y
with B(D_n) -> 1 and J_pi(D_n) -> 0. Nevertheless every plan sequence on Y with
B(D_n) -> 1 has liminf_n Tail_T(D_n) >= h_S > 0 for every T. Hence the
fixed-cutoff uniform-integrability hypothesis of
`fpbs-binary-entropy-traffic-tail-bound` is strictly stronger than cost
preservation for that group, and it is never available over a source action
of cost one of any nonamenable finitely generated group.

## 3. Augmentation

**Lemma 4.** From D construct D^+ as follows. Restrict every copy phi_j to
its used set U_j, keeping all chosen routes. For each s in S add a new copy
psi_s = T_s|(Y minus E_s), and route each uncovered request (s,y) by the single
forward hop along psi_s at y. Then D^+ is a finite routing plan with
r(D^+) = 0, B(D^+) = B(D), and Tail_T(D^+) = Tail_T(D) for every T >= 0.
Every y is joined to ys, for every s, by a path of used copies of D^+, so the
components of the graph of used copies are whole Gamma-orbits.

*Proof.* Routes of D use only used copies, so restricting domains to U_j keeps
them valid and leaves every k_j unchanged. The new copy psi_s at a point z is
used only by the request (s,z): old routes use old copies, and each new route
uses only its own copy. Hence the new traffic is identically one on
Y minus E_s, its used set has measure nu(Y minus E_s), and its Q vanishes. So

    B(D^+) = sum_j nu(U_j) + sum_s nu(Y minus E_s) = B(D),

every tail is unchanged, and all requests are covered. The path-length bound
is max(L,1), and measurability is clear. Since S generates Gamma, chaining the
generator routes (in either direction) connects y to every yg. QED

## 4. Finite connected cells with large classes

Let H be the graph on Y whose edges are given by finitely many measurable
edge copies (partial maps T_{g_i}|A_i), and let d_H be its path distance.
The ball B_H(y,r) is the set of points reachable by words of length at most
r in these maps and their inverses, so it is finite, and for a Borel set W
the set of y with a point of W in B_H(y,r) minus {y} is Borel.

**Lemma 5.** Assume every component of H is infinite, and fix an integer
R >= 1. There are a Borel set M of markers, a Borel map c: Y -> M with
c(m) = m on M, and a Borel set P of edge copies of H such that, with
K(y) = c^{-1}(c(y)):

(i) each class K(y) is finite and contains B_H(c(y),R), hence has at least
R+1 points;

(ii) every copy in P joins two points of one class, and m(P) = nu(Y minus M);

(iii) nu(M) = integral 1/|K(y)| dnu(y) <= 1/(R+1).

*Proof.* **Markers.** Let G be the graph joining x != y when d_H(x,y) <= 2R.
It is generated by the finitely many words of length at most 2R, so it is a
locally finite Borel graph in the sense above. Fix a countable family (W_n)
of Borel sets, closed under finite intersections, such that for x != y some
W_n contains x but not y (for instance a countable base of a Polish topology
generating the Borel structure). Each x has finitely many G-neighbours, so
intersecting finitely many such sets gives some W_n that contains x and none
of them. Let col(x) be the least such n. It is Borel, and it is a proper
colouring: if x ~ y and col(x) = col(y) = n, then y is a neighbour of x in
W_n. Put M_0 empty and

    M_{n+1} = M_n union {x : col(x) = n, no G-neighbour of x lies in M_n}.

Points of one colour are pairwise non-adjacent, so each M_n is Borel and
independent. The union M is independent, and it is maximal: a point x not in
M with col(x) = n was rejected at stage n+1, so it has a neighbour in M_n.
Thus distinct markers are at H-distance greater than 2R, and every point is
within distance 2R of M. (This is the familiar greedy construction of Borel
maximal independent sets in locally finite Borel graphs; it is written out
because only this elementary case is used.)

**Cells.** Fix a Borel injection iota: Y -> R. Let c(x) be the marker in
B_H(x,2R) minimizing the pair (d_H(x,m), iota(m)) lexicographically. The
candidate set is finite and nonempty, so c is Borel, and c(m) = m. The class
of m lies in B_H(m,2R), so it is finite. If d_H(x,m) <= R and m' != m is a
marker, then d_H(x,m') >= d_H(m,m') - d_H(x,m) > 2R - R >= d_H(x,m), so
c(x) = m. The component of m is infinite and connected with finite balls, so
some point lies at distance more than R, and a geodesic to it passes through
points at each distance 0,...,R. This proves (i).

**Parent copies.** Let x not be a marker, m = c(x), d = d_H(x,m) >= 1. Among
the finitely many hops from x (copy index and direction) to a point x' with
d_H(x',m) = d-1, choose the first in a fixed order. A geodesic exists, so the
choice exists and is Borel. We claim c(x') = m. Otherwise m' = c(x') != m
satisfies (d_H(x',m'), iota(m')) < (d_H(x',m), iota(m)). If
d_H(x',m') < d-1 then d_H(x,m') < d, contradicting c(x) = m. If
d_H(x',m') = d-1 and iota(m') < iota(m) then d_H(x,m') <= d and
iota(m') < iota(m). In both cases m' lies in B_H(x,2R) and beats m for x,
which is a contradiction.

Let P be the set of chosen copies. A chosen copy has both endpoints in the
class of m, at distances d and d-1 from m, so it determines its child x as
the endpoint farther from m. The map from x to its chosen copy is therefore
injective. On the Borel piece where the hop is copy i forward, the copy's
forward starting point is x. Where it is copy i backward, the starting point
is x g_i^{-1}, a measure-preserving partial injection. Hence
m(P) = nu(Y minus M), proving (ii).

Each class contains exactly one marker, so (5.2) below with F = 1_M gives
nu(M) = integral 1/|K(y)| dnu, and (i) gives (iii). QED

The classes K(y) are subsets of H-components, hence of Gamma-orbits. Thus K
is a Borel subequivalence relation of the orbit relation with finite classes.

## 5. The boundary count

Use the mass transport identity for the orbit relation of a free p.m.p.
action. For Borel Phi >= 0 on pairs (y, yg),

    integral sum_g Phi(y, yg) dnu(y) = integral sum_g Phi(y g^{-1}, y) dnu(y),     (5.1)

term by term by invariance of nu under T_{g^{-1}}. If K is a Borel
subequivalence relation of the orbit relation with finite classes K(y), and
F >= 0 is Borel, applying (5.1) to Phi(y,z) = F(y) 1_{z in K(y)} / |K(y)| gives

    integral F dnu = integral (1/|K(y)|) sum_{z in K(y)} F(z) dnu(y).             (5.2)

**Lemma 6.** For every Borel subequivalence relation K of the orbit relation
with finite classes,

    integral #{s in S : ys not in K(y)} dnu(y) >= h_S.

*Proof.* By freeness K(y) = yF_y for a unique finite set F_y containing the
identity. For z = yg in K(y), #{s : zs not in K(y)} = #{s : gs not in F_y},
since yg s = yg' with g' in F_y forces gs = g'. Summing over g in F_y,

    sum_{z in K(y)} #{s : zs not in K(y)} = |{(g,s) in F_y x S : gs not in F_y}|
                                        >= h_S |K(y)|.

Divide by |K(y)| and integrate using (5.2). QED

## 6. Proofs

**Proof of Theorem 1.** By Lemma 4 we may replace D by D^+: B and every
tail are unchanged. Now r(D) = 0, and the graph H of used copies has whole
orbits as components. These are infinite because Gamma is infinite.

Fix R >= 1 and take M, c, P, K from Lemma 5 applied to H. Let X be the set of
used copies whose two endpoints lie in different classes. The sets X and P
are disjoint sets of used copies, so by Lemma 5(ii),(iii)

    m(X) <= sum_j nu(U_j) - m(P) = B(D) - 1 + nu(M) <= B(D) - 1 + 1/(R+1).   (6.1)

Let ys not lie in K(y). The chosen route tau_s(y) visits points
y = v_0, v_1, ..., v_l = ys, consecutive points joined by used copies. Since
v_0 is in K(y) and v_l is not, some hop joins two different classes, so it
uses a copy of X. Thus 1_{ys not in K(y)} is at most the number of occurrences
of copies of X on tau_s(y). By Lemma 6 and (1.1) with f_j the indicator of X,

    h_S <= integral sum_s 1_{ys not in K(y)} dnu(y)
        <= sum_j integral k_j 1_X(j,.) dnu.                                   (6.2)

On a used copy, k_j = Q_j + 1. If Q_j <= T then k_j <= T+1, and otherwise
k_j = Q_j + 1 <= Q_j + T + 1. So pointwise k_j <= T + 1 + Q_j 1_{Q_j > T}, and

    sum_j integral k_j 1_X(j,.) dnu <= (T+1) m(X) + Tail_T(D)
                                    <= (T+1)(B(D) - 1 + 1/(R+1)) + Tail_T(D).

Let R -> infinity. QED

For amenable infinite Gamma the same chain, with h_S replaced by 0, first
letting R -> infinity and then T -> infinity (a finite plan has bounded
traffic, so Tail_T(D) = 0 for large T), gives B(D) >= 1. This reproves the
familiar cost lower bound for plans and is not needed below.

**Proof of Corollary 2.** (a) If all traffic is at most M >= 1, take
T = M - 1. Then Q_j <= T everywhere, so Tail_T(D) = 0, and (2.1) gives
h_S <= M (B(D) - 1). A finite plan has bounded traffic. If it has no used
copy then B(D) = |S| >= 2, because a cyclic group is amenable. So B(D) > 1
always.

(b) This is immediate from (2.1): Tail_T(D_n) >= h_S - (T+1)(B(D_n) - 1).

(c) For T > 0 we have Q 1_{Q > T} <= Q^2 / T, so
sum_j integral Q_j^2 >= T Tail_T(D) >= T (h_S - (T+1) eps). Take
T = (h_S - eps)/(2 eps). If eps < h_S this is positive, and
h_S - (T+1) eps = (h_S - eps)/2, giving (h_S - eps)^2/(4 eps). If
eps = h_S the bound is zero.

(d) By (a) B(D_n) > 1. By (2.1), (T_n + 1)(B(D_n) - 1) >= h_S - Tail_{T_n}(D_n),
which is at least h_S/2 for large n. Since B(D_n) - 1 -> 0, eventually
h_S/(2(B(D_n) - 1)) >= 2, hence T_n >= h_S/(2(B(D_n) - 1)) - 1
>= h_S/(4(B(D_n) - 1)). Then H_n/(B(D_n) - 1) <= 4 T_n H_n / h_S -> 0. QED

**Proof of Corollary 3.** Gamma = F_2 x Z contains F_2, so it is nonamenable.
By the imported theorem of `fpbs-khezeli-products-have-fixed-price-one`
(arXiv:2509.08325) every free p.m.p. action of a product of two infinite
countable groups has cost one, so C(X) = C(Y) = 1. The established
`fpbs-traffic-variational-cost-identities` gives
C(X) = inf over plans D on Y of B(D) + J_pi(D), for a finitely generated
group and finite-cost base. Choose D_n with B(D_n) + J_pi(D_n) -> 1. Since
B(D_n) >= C(Y) = 1 and J_pi >= 0, we get B(D_n) -> 1 and J_pi(D_n) -> 0.
Corollary 2(b) applies to every sequence with B(D_n) -> 1.

For the last assertion, let Gamma be any nonamenable finitely generated group
and C(Y) = 1. Source-near-optimal plans are those with B(D_n) -> C(Y) = 1,
and Corollary 2(b) shows that sup_n Tail_T(D_n) >= h_S for every T. Hypothesis
(3) of `research/artifacts/fpbs/docs/binary-descent-entropy-tail.md` therefore
fails for every such sequence. QED

## 7. What this does and does not rule out

**The mechanism.** A cheap plan has budget only slightly above one, and a
spanning forest of large finite cells already uses budget one. The copies
crossing between cells therefore have measure at most B - 1 + o(1). Lemma 6
says the generator requests leaving the cells have measure at least h_S,
independently of the plan. Every such request crosses a crossing copy, so the
crossing copies carry traffic at least h_S on a set of measure about B - 1.
This is a max-flow/min-cut congestion count. Arbitrary group labels do not
help, because the cells are built from the plan's own used graph, not from a
Cayley graph.

**Answer to the scope question on the target.** The scope audit of
`fpbs-correlated-reuse-flags-removable` records that the fixed-cutoff
uniform-integrability form of the entropy-tail criterion "implies cost
preservation but is not known to follow from it". Corollary 3 settles this.
For F_2 x Z, and for every nonamenable finitely generated group with fixed
price one, cost is preserved by every free factor map, yet no
source-near-optimal plan sequence has uniformly integrable repeated traffic.
So the fixed-cutoff form is strictly stronger than preservation. It is never
available when the source has cost one and the group is nonamenable.

**Consequence for the live Bernoulli route.** On the product projection
a x b -> b used by `fpbs-bernoulli-lower-bound-from-reuse-removal`, the source
cost is C(a x b) = C(a) by `fpbs-bernoulli-noise-does-not-change-cost`. For a
nonamenable group with some free action of cost one, which is exactly the
setting of a hypothetical counterexample with infimal cost one and Bernoulli
cost above one, criterion (3) of the entropy-tail artifact can never be
verified over that source. Corollary 2(a) also excludes near-optimal plans of
uniformly bounded congestion over such a source. The largest traffic must be
at least h_S/(B - 1). Any removal argument there must tolerate traffic peaks
of that order.

**What survives.** The moving-cutoff form, with T_n H_n -> 0 and
Tail_{T_n}(D_n) -> 0, is not excluded. Corollary 2(d) makes it quantitative
over a cost-one source: it needs T_n of order at least h_S/(B_n - 1), hence a
total one-site flag entropy H_n = o(B_n - 1). In words, the reuse flags must
become deterministic given the base faster than the budget excess vanishes.
Lifted base plans have H = 0. When C(X) = C(Y) = 1, lifts of near-optimal
base plans are source-near-optimal. Each has bounded traffic, but by Corollary
2(a) the bounds grow at least like h_S/(B_n - 1). Letting T_n exceed them
satisfies the moving-cutoff condition, consistent with Corollary 2(d). This
matches the target's equivalence remark: any plan property that lifts from the
base and forces J -> 0 is equivalent to preservation. Corollary 2 shows only
that, over cost-one sources, the growth of the cutoffs cannot be avoided.

**What this does not touch.**

* The defect J_pi itself. By Corollary 3, heavy tails and J -> 0 coexist.
  The obstruction concerns the tail sufficient condition, not the defect.
* Sources of cost above one. When (T+1)(B - 1) >= h_S, inequality (2.1) is
  vacuous. For F_2 with a free basis, direct edges give B = 2 and traffic one.
  Whether uniform integrability can fail over sources of cost above one is not
  addressed.
* Route lengths. `fpbs-quantitative-routing-tail-bound` forces long routes for
  invariant spanning subgraphs of a Cayley graph with half expected degree
  near one. Theorem 1 forces congestion for plans with arbitrary labels. The
  total route length equals sum_j integral k_j, which Theorem 1 does not force
  to diverge. Neither statement is derived from the other here.
* Fixed Price, the target claim, and every named live route. None is proved
  or invalidated. The result removes one proposed sufficient condition from
  the price-one regime and quantifies the condition that remains.

## 8. Evidence and sources

**Finite replay.**
`experiments/fpbs-cost-one-plans-heavy-traffic-2026-09-16/replay_crossing_bound.py`
writes `replay_results.json` in the same directory, with status passed. It
ran 160 random plans with random labels and domains over Z/40, Z/12 x Z/6,
S_4 and A_5, with cutoffs T in {0, 1/2, 1, 2, 3, 5}. Exact rational arithmetic
checks:

* identity (1.1) with f = 1;
* that augmentation preserves B and all tails and covers all requests;
* the marker, Voronoi-cell and parent-tree properties of Lemma 5;
* the crossing-measure bound (6.1) with nu(M) in place of 1/(R+1);
* the pointwise traffic bound;
* the chain boundary(K) <= (T+1) m(X) + Tail_T <= (T+1)(B - 1 + nu(M)) + Tail_T.

A finite group has h_S = 0, so the replay cannot test Lemma 6 or the
infinite-group statements. It checks only the finite counting steps.

**Sources.**

* Routing formalism, identity (1.1), Theorems 4.1 and 5.1:
  `research/artifacts/fpbs/docs/fixed-price-conditional-traffic.md`, an
  established repository node.
* Entropy-tail criterion and its hypothesis (3):
  `research/artifacts/fpbs/docs/binary-descent-entropy-tail.md`.
* Fixed price one for products of infinite groups: A. Khezeli,
  arXiv:2509.08325, as imported by
  `fpbs-khezeli-products-have-fixed-price-one`. Not re-fetched in this session.
* The Borel maximal independent set construction is standard in descriptive
  set theory, e.g. Kechris--Solecki--Todorcevic, *Borel chromatic numbers*,
  Adv. Math. 1999. That source was not fetched here and no theorem number is
  asserted. Section 4 proves the needed case directly.
* Related background, not used in the proofs: Lyons--Pichot--Vassout
  (arXiv:0711.0393) and Pichot--Vassout (arXiv:0903.0911), as cited in
  `research/artifacts/fpbs/docs/isoperimetric-test-descent.md`. They were not
  fetched in this session, so any relation to Theorem 1 is unverified.

**Status.** Written deduction with a passing finite replay of the counting
steps. Not refereed and not formally verified. No novelty claim.
