# Perturbative reuse removal fails for every infinite finitely generated group

Research derivation, September 17, 2026 (swarm-0917, worker w5-fp-reuse-flags).

## 0. What this note does

`fpbs-perturbative-reuse-removal-fails` (wave 4) proved on one free factor of
Z that some optimal source plan admits no small-defect near-optimal plan
within small used-edge distance. Its Section 5 left open whether perturbative
removal fails for every infinite finitely generated group, because its
counting step (every request needs two light steps) used the arithmetic of Z.

This note settles that question for every infinite finitely generated group
Gamma, every free factor pi_0: Y_0 -> X, and the noise extension
Y = Y_0 x ([0,1]^Gamma, Leb) with pi = pi_0 o pr. It does so in a metric that
depends only on the used graph, not on how edges are split into copies or
oriented. The proof has two independent prerequisites, each of which could
have failed:

* (P1) **Small-defect near-optimal plans need base-determined edges.** If the
  request set S has |S| > C(Y), a plan with defect delta and budget at most
  C(Y) + beta has heavy occurrences of measure at least
  (|S| - C(Y) - beta - delta)/(2|S|) (Proposition 3.1). Its proof needs only
  one light step per request, so it holds for every group.
* (P2) **Near-optimal plans with every edge occupancy at most 1/2 exist.** By
  relocating a near-optimal generating graph inside large Borel Voronoi cells
  with a uniformly random permutation drawn from the noise, one gets plans D_n
  with B(D_n) -> C(Y) and E[m_h | pi] <= 1/2 for every label h
  (Proposition 4.2).

Together with the L1 stability of occupancy (Lemma 2.2 here), these give
Theorem 5.1. Every plan D' with B(D') <= C(Y) + beta and J_pi(D') <= delta has

    d_G(D_n, D') >= (|S| - C(Y) - beta - (1 + 8|S|) delta) / (6|S|).

Status: written deduction over established claims of this graph. There is no
experiment, and no originality or independent validation is claimed. Fixed
Price and the target claim `fpbs-correlated-reuse-flags-removable` are
neither proved nor refuted.

## 1. Setting and the graph metric

Notation is that of `research/artifacts/fpbs/docs/fixed-price-reuse-compression.md`,
Section 1 (right actions, finite routing plans, traffic identity (1), budget
(2), formula (3) C(Y) = inf B). Gamma is an infinite group with a finite
generating set S, e not in S, and |g| is word length. Freeness makes the orbit
metric rho(y, y g) = |g| well defined. A plan D has partial maps
phi_j = T_{g_j}|A_j, covered sets E_s, paths tau_s(y) from y to y s, traffic
N_j, r = sum_s nu(Y \ E_s) and B = r + sum_j nu(N_j >= 1). Its defect is
J_pi(D) = sum_j integral min(a_j, b_j) dmu, with a_j = P(N_j = 0 | pi),
b_j = E[(N_j - 1)_+ | pi], and occupancy O_j = 1 - a_j (claim
`fpbs-traffic-defect-is-total-variation-loss`). Copies with g_j = e are loops.
Deleting loop steps from paths never increases B or J, so we may assume there
are none.

**Graph multiplicity.** For h in Gamma and z in Y let

    m_h(z) = #{ j : g_j = h, z in A_j, N_j(z) >= 1 }
           + #{ j : g_j = h^{-1}, z h in A_j, N_j(z h) >= 1 },

the number of used copies realizing the unordered edge {z, z h}. Put

    d_G(D, D') = sum_h integral_Y | m_h - m'_h | dnu.

With wave 4's multiplicity n_g(y) = #{j : g_j = g, N_j(y) >= 1} one has
m_h = n_h + n_{h^{-1}} o T_h, so d_G <= 2d, where d is wave 4's copy metric. Every
lower bound for d_G halves to a lower bound for d.

**Why the graph metric.** d depends on bookkeeping. Take a plan with J = 0
lifted from the base, and re-own each used edge {y, y g}: charge it to the
label g copy at y when xi(y) < xi(y g), and to the label g^{-1} copy at y g
otherwise, where xi is independent noise. This changes neither the graph nor
the traffic along edges, and it changes d by a macroscopic amount. The split
copies have occupancy 1/2, so J becomes positive. The graph metric ignores
such re-owning, so a lower bound in d_G is a statement about the graph that
must be changed.

Two facts, as in wave 4 but for m:

    sum_{j : g_j = h} 1_{N_j >= 1} <= n_h <= m_h,  hence  sum_{j : g_j = h} O_j <= E[m_h | pi];   (1.1)
    integral | E[m'_h | pi] - E[m_h | pi] | dmu <= integral | m'_h - m_h | dnu.                 (1.2)

(1.2) is the L1 contraction of conditional expectation.

## 2. Imported lemma and graph-metric stability

**Lemma 2.1** (established claim `fpbs-small-defect-reuse-on-high-occupancy-edges`,
wave-4 artifact Section 2, any countable group, any free factor). For a plan D
and 0 < c < 1 put W_j = {a_j >= c, b_j < c}. Call a used occurrence (j, z)
light if pi(z) is in W_j and heavy otherwise. Then, verbatim from that claim:
"the heavy occurrences have measure at most sum_j integral over {a_j < c} of
O_j, plus J_pi(D)/c; the total light traffic is at most (B - r) + J_pi(D)."

**Lemma 2.2 (graph version).** Let D, D' be plans, let h be a label with
E[m_h | pi] <= 1/2 mu-a.e., and let 0 < c < 1/2. Then

    sum_{j : g'_j = h} integral_{ {a'_j < c} } O'_j dmu <= ( 1/(1 - 2c) + 1 ) integral | m'_h - m_h | dnu.

*Proof.* Put e = |E[m'_h - m_h | pi]| and F = {e > 1/2 - c}. If a'_j(x) < c
for a copy of label h, then by (1.1) E[m'_h | pi](x) >= O'_j(x) > 1 - c, and
since E[m_h | pi] <= 1/2 this forces x in F. So by (1.1), then (1.2) and
Markov's inequality,

    sum_j integral_{ {a'_j < c} } O'_j <= integral_F E[m'_h | pi] dmu
        <= integral_F ( 1/2 + e ) dmu <= mu(F)/2 + integral e dmu
        <= ( 1/(1 - 2c) + 1 ) integral | m'_h - m_h | dnu.   QED.

**Corollary 2.3.** If E[m_h | pi] <= 1/2 for every h, then for every plan D'
with J_pi(D') <= delta, taking c = 1/4, the heavy occurrences of D' have
measure

    eta' <= 3 d_G(D, D') + 4 delta.                                          (2.1)

*Proof.* Sum Lemma 2.2 over h and apply the heavy-occurrence bound of Lemma
2.1. QED.

## 3. Prerequisite P1: small-defect plans need heavy mass once |S| > C

**Proposition 3.1.** Let D' be a plan for any free factor pi of any countable
group with finite request set S (e not in S). Let eta' be the measure of its
heavy occurrences at some 0 < c < 1. Then

    B(D') >= |S| - J_pi(D') - 2 |S| eta'.                                     (3.1)

*Proof.* For a covered request y in E_s let u_s(y) be the number of light
occurrences on tau_s(y). The traffic identity (1) of the compression artifact
(the change of variables in `fpbs-conditional-traffic-descent-bound`), applied
with h_j = 1_{W_j} o pi, and the light-traffic bound of Lemma 2.1 give

    sum_s integral_{E_s} u_s dnu = sum_j integral_{pi^{-1} W_j} N'_j dnu <= (B' - r') + J'.   (3.2)

Since s != e, every path tau_s(y) has at least one step. If u_s(y) = 0, the
first step is a heavy occurrence (j, z) with y = z (forward traversal) or
y = z g_j (reverse traversal). The starts of heavy occurrences have measure
eta', and T_{g_j} preserves measure, so these y have measure at most 2 eta'.
Hence integral_{E_s} u_s >= nu(E_s) - 2 eta', and summing over s,

    sum_s integral_{E_s} u_s dnu >= |S| - r' - 2 |S| eta'.                   (3.3)

Comparing (3.2) and (3.3) gives (3.1). QED.

Reading: when |S| > C(Y), a plan with budget close to C(Y) and small defect must
put heavy mass at least about (|S| - C(Y))/(2|S|) on edges of occupancy above
1 - c. For every infinite finitely generated group some such S exists: C(Y) <=
|S_0| for any generating set S_0, and adding one element outside S_0 and e
gives |S| > C(Y). This is the group-free replacement for wave 4's Step 3, which
needed two light steps per request and used the arithmetic of Z.

## 4. Prerequisite P2: near-optimal plans with every occupancy at most 1/2

Fix a free p.m.p. action on (Y_0, nu_0), a free factor pi_0: Y_0 -> X, and
Y = Y_0 x ([0,1]^Gamma, Leb^Gamma) with the diagonal action (shift on the
second factor), pi = pi_0 o pr. Put xi(y_0, omega) = omega(e). For distinct
g, xi(y g) reads distinct coordinates of omega, so given y_0 the values
xi(y g), g in Gamma, are i.i.d. uniform. By the established claim
`fpbs-bernoulli-noise-does-not-change-cost` ("C(a x b) = C(a)"),
C(Y) = C(Y_0) =: C.

**Lemma 4.1 (Borel cells).** For every R >= 2 there is a Borel partition of
Y_0 into finite sets (cells), each contained in the orbit of a point,
measurable with respect to Y_0, such that each cell contains an orbit ball
of radius ceil(R/2) - 1 and is contained in an orbit ball of radius R - 1.

*Proof.* Let F = {g : 1 <= |g| <= R - 1}. Fix a countable Boolean algebra
{U_n} of Borel sets separating points of Y_0. Since y != y g for g in F,
for each y some U_n contains y and no y g with g in F. Let col(y) be the least
such n. This is Borel, and rho(y, y') < R, y != y' implies col(y) != col(y').
Greedily put M_0 = empty and M_{n+1} = M_n union {y : col(y) = n, no point of
M_n within rho-distance < R}. Points of one colour are at distance >= R from
each other, so M = union M_n is R-separated, Borel and maximal: a point of
colour n not in M was rejected at stage n + 1 because of a point of M_n at
distance < R. Assign each y to its nearest point of M, breaking ties by the
least g in a fixed enumeration of Gamma with y g in M. Maximality gives
distance <= R - 1. If rho(y, p) < R/2 for p in M, any other q in M with
rho(y, q) <= rho(y, p) would give rho(p, q) < R, which is impossible, so the
ball of radius ceil(R/2) - 1 about p lies in the cell of p. QED.

Lift the cells to Y through pr. Every cell of Y is a finite subset of an orbit,
determined by the Y_0-coordinate. Order each cell canonically by the fixed
enumeration of the g with cell point p g, where p is its centre.

**Relocation psi.** On each cell, send the k-th point in canonical order to
the point with the k-th smallest value of xi (ties have probability zero).
Then psi: Y -> Y is Borel, a bijection on every cell, and of the form
psi(y) = y gamma(y) with |gamma(y)| <= 2(R - 1). A Borel map in the full
group that is bijective preserves nu, by partitioning into the finitely many
pieces {gamma = g}. Given the Y_0-coordinate, the restrictions of psi to the
cells are independent uniformly random permutations, because the xi-ranks
inside distinct cells come from disjoint i.i.d. coordinates.

**Proposition 4.2.** There are finite routing plans D_n for (Y, pi, S) with
B(D_n) -> C and E[m^{(n)}_h | pi] <= 1/2 mu-a.e. for every h in Gamma.

*Proof.* *Step 1: a generating graph on Y_0.* By formula (3) of the compression
artifact choose a plan L_n on Y_0 with B(L_n) <= C + 1/n. Let G be the
graphing consisting of the used restrictions T_{g_j}|{N_j >= 1} of L_n together
with the direct repairs T_s|(Y_0 \ E_s). Let K be the number of these partial
maps. The cost of G is B(L_n). Every request y -> y s is joined by a path in G,
and S generates, so G generates the orbit relation. Lift G to Y through pr.
Its cost is unchanged, and it still generates because the action on Y is free.

*Step 2: relocation.* Choose R with |ball of radius ceil(R/2) - 1| >= 4K + 1.
This is possible because Gamma is infinite. Take the cells and psi of Lemma
4.1 for this R. Define psi(G): for the i-th map T_{g_i}|A_i of G and each
label h, let

    A'_{i,h} = { psi(y) : y in A_i, psi(y) h = psi(y g_i) },  h = gamma(y)^{-1} g_i gamma(y g_i).

Only finitely many h occur (|h| <= 4(R - 1) + |g_i|), and
sum_h nu(A'_{i,h}) = nu(A_i) because psi preserves nu. So psi(G) is a finite
graphing of cost B(L_n). On each orbit, psi is a bijection carrying G-edges to
psi(G)-edges, so psi(G) is connected on orbits and generates. As in the proof
of formula (3), choose a Borel shortest-path selection in psi(G) and a length
bound L covering all but 1/n of each request. Pruning unused copies gives a
plan D_n with B(D_n) <= B(L_n) + |S|/n -> C, and B(D_n) >= C by (3).

*Step 3: occupancy.* Fix z in Y and h != e, and condition on the
Y_0-coordinate of z. Index the orbit of z as z g, g in Gamma. Cells and the
sets A_i depend only on Y_0-coordinates, so which indices form cells and which
lie in A_i is fixed, and only psi is random. A
used copy of D_n realizing {z, z h} comes from some map i of G and some orbit
point y in A_i, with either psi(y) = z and psi(y g_i) = z h, or psi(y) = z h
and psi(y g_i) = z. Since psi preserves cells, the first case needs y in the
cell C(z). Given Y_0, the events are about a uniform random permutation of
C(z) and, when y g_i lies in another cell C', an independent one of C'. So

    P( psi(y) = z, psi(y g_i) = z h | Y_0 ) <= (1/|C(z)|) * 1/(c_min - 1),

where c_min >= 4K + 1 is the minimal cell size. The first factor is uniformity
on C(z). The second is 1/(|C(z)| - 1) when y g_i is in C(z), and 1/|C'| or 0
otherwise. Summing over the |C(z)| points y of C(z) and the at most K maps i
with y in A_i bounds the first case by K/(c_min - 1). The same bound with C(z h)
holds for the second case. Hence

    E[m^{(n)}_h(z) | Y_0] <= 2K/(c_min - 1) <= 1/2.

For h = e, m_h = 0, since psi is injective and G has no loops. Since pi factors
through Y_0, E[m_h | pi] = E[ E[m_h | Y_0] | pi ] <= 1/2. QED.

## 5. The theorem

**Theorem 5.1.** Let Gamma be an infinite finitely generated group, pi_0: Y_0 -> X
a free factor, Y = Y_0 x [0,1]^Gamma, pi = pi_0 o pr, and S a finite generating
set with e not in S and |S| > C = C(Y). Let D_n be the plans of Proposition 4.2.
Every finite routing plan D' for (Y, pi, S) with B(D') <= C + beta and
J_pi(D') <= delta satisfies, for every n,

    d_G(D_n, D') >= ( |S| - C - beta - (1 + 8|S|) delta ) / (6 |S|),

and hence d(D_n, D') >= ( |S| - C - beta - (1 + 8|S|) delta ) / (12 |S|).

*Proof.* By Proposition 4.2 and Corollary 2.3, eta' <= 3 d_G + 4 delta. By
Proposition 3.1,

    C + beta >= B(D') >= |S| - delta - 2|S| (3 d_G + 4 delta).

Rearrange, and use d_G <= 2d. QED.

**Corollary 5.2 (open balls).** If d_G(D_n, D'') <= eps_0, then every D' as above
has d_G(D'', D') >= (|S| - C - beta - (1 + 8|S|) delta)/(6|S|) - eps_0.

**Corollary 5.3 (defect of the relocated plans).** Taking D' = D_n and
beta_n = B(D_n) - C -> 0 gives J_pi(D_n) >= (|S| - C - beta_n)/(1 + 8|S|). So the
relocated plans carry defect bounded below, although J = 0 plans of budget near
C exist (lift a near-optimal base plan when C(X) = C, which holds, for example, for
X = Y_0 and pi_0 = id).

## 6. What is killed, and where every member dies

**The class.** A *graph-perturbative removal statement* for a family F of free
factors (pi, S) says: for every sequence of source plans D_n with
B(D_n) -> C(Y), there are plans D'_n with d_G(D_n, D'_n) -> 0,
B(D'_n) -> C(Y) and J_pi(D'_n) -> 0. This covers every procedure that repairs a
given near-optimal plan by changing a vanishing measure of the used graph:
deleting, adding or re-routing sparse edges, recoding flags on small regions,
and any re-owning or re-orientation of copies (these cost nothing in d_G).
Since d_G <= 2d, the class contains wave 4's copy-metric class.

**It is false for every infinite finitely generated group** and for every
family F that contains, for some free factor pi_0 of that group, the noise
extension (Y_0 x [0,1]^Gamma, pi_0 o pr) with some S with |S| > C. By Theorem
5.1 any repair must change at least (|S| - C)/(6|S|) of the used graph, less
O(beta + delta). Wave 4 had this only for one factor of Z. Here it holds for
all groups, all base actions and all free factors after adding noise, which is
the setting where the target claim is needed (compare
`fpbs-bernoulli-lower-bound-from-reuse-removal`).

**The invariant** is the base-conditional edge occupancy E[m_h | pi]. It is
graph-intrinsic, and edits move it only in L1 (Lemma 2.2).

**The step where every member dies** is Proposition 3.1 combined with Lemma
2.1. A small-defect plan with budget near C must route a macroscopic
fraction, (|S| - C)/(2|S|), of first steps over heavy occurrences, which lie on
copies of occupancy above 3/4 or over rare base regions. A relocated plan D_n
has every occupancy at most 1/2, so heavy mass can only come from the d_G-edit.

**What survives.**

* Cost preservation itself. Nothing here is a counterexample to the target
  claim or to Fixed Price. The target stays OPEN.
* Removal with macroscopic edits: a global rebuild whose cost is explicitly
  bounded but not small. Theorem 5.1 says such a rebuild must replace a
  constant fraction of the graph.
* Restricted statements (form (II) of the target's scope audit) that choose
  their source plans. Plans lifted from the base already have J = 0.
  Statements for families of factors not closed under noise extension are also
  untouched, and so are statements for request sets with |S| = C. For those,
  Proposition 3.1 gives nothing, and the only known kill is wave 4's
  copy-metric Z example.

**Diagnostic.** A proposed removal procedure acting on arbitrary near-optimal
plans must, on the relocated plans D_n, change a constant fraction of the used
graph. On D_n every copy has occupancy at most 1/2. So recoding which copies
carry flags, or who owns them, cannot remove the defect. The used edges
themselves must move.

## 7. Scope and caveats

* The kill needs |S| > C(Y). This is no restriction on the group (add a
  redundant generator), but it is a restriction on the request set of the
  removal statement. For groups with C(Y) = rank the minimal generating sets
  are not covered.
* The constants 6 and 8 are not optimised.
* The noise extension is used only to make psi independent of the base.
  The proof works verbatim whenever pi factors as Y -> Y_0 -> X with Y
  isomorphic over Y_0 to Y_0 x [0,1]^Gamma. Factors with no such splitting are
  not covered.
* Lemma 4.1 is a self-contained greedy construction. It uses only a countable
  separating algebra of Borel sets and the finiteness of balls, and imports no
  descriptive set theory.

## References

* Compression artifact: `research/artifacts/fpbs/docs/fixed-price-reuse-compression.md`,
  Section 1 (plans, identity (1), budget (2), formula (3)).
* `fpbs-small-defect-reuse-on-high-occupancy-edges` and
  `research/artifacts/fpbs-perturbative-reuse-removal-fails-2026-09-17.md`,
  Section 2 (Lemma 2.1).
* `fpbs-traffic-defect-is-total-variation-loss` (defect as overlap).
* `fpbs-conditional-traffic-descent-bound` (traffic change of variables).
* `fpbs-bernoulli-noise-does-not-change-cost` (C(Y_0 x [0,1]^Gamma) = C(Y_0)).
* `fpbs-perturbative-reuse-removal-fails` (the Z, copy-metric predecessor).
