# Perturbative reuse removal fails: small edits cannot remove the traffic defect

Research derivation, September 17, 2026 (swarm-0917, worker w4-fp-reuse-flags).

## 0. What this note does

The scope audit of `fpbs-correlated-reuse-flags-removable` records that the
claim, as stated, is cost preservation itself, and that a removal statement
which genuinely reduces the problem must either (I) derive new plans from
*arbitrary* source-near-optimal plans through edits of explicitly bounded
cost and defect, or (II) be restricted to a family of factor maps or groups.

This note kills the perturbative subclass of (I): removal procedures whose
edits have measure tending to zero. On one fixed free factor of Z, where every
free action has cost one, there is an exactly optimal plan D (B = 1, J = 1)
such that every plan D' with B(D') <= 1 + beta and J(D') <= delta differs from D
in used-edge measure by at least (1 - 2 beta - 81 delta)/65. The mechanism is a
general lemma (Section 2): a plan of small defect carries its repeated traffic
only on edges whose base-conditional occupancy is close to one, or over rare
base regions. Small edits preserve conditional occupancy in L1, and an
optimal plan whose budget sits on noise-split labels has no high-occupancy
edges at all.

Status: written deduction with a finite exact replay of the plan's traffic
(`experiments/fpbs-perturbative-reuse-removal-2026-09-17/parity_plan_verifier.py`).
No originality or independent validation is claimed. Fixed Price and the
target claim are neither proved nor refuted.

## 1. Setting and the invariant

Notation is that of `research/artifacts/fpbs/docs/fixed-price-reuse-compression.md`,
Sections 1--3. A finite routing plan D on a free factor pi: (Y,nu) -> (X,mu)
has edge copies j with group labels g_j, requests s in S covered on E_s with
paths tau_s(y), traffic N_j, uncovered mass r = sum_s nu(Y \ E_s) and budget
B = r + sum_j nu(N_j >= 1). Its defect is (formula (9) there, the claim
`fpbs-traffic-defect-is-total-variation-loss`)

    J_pi(D) = sum_j integral min(a_j, b_j) dmu,
    a_j = P(N_j = 0 | pi),   b_j = E[(N_j - 1)_+ | pi].

Write O_j = P(N_j >= 1 | pi) = 1 - a_j, the **conditional occupancy** of copy j.

**Used-edge multiplicity.** For g in Gamma put
n_g(y) = #{ j : g_j = g, N_j(y) >= 1 }, and for plans D, D' define

    d(D, D') = sum_g integral_Y | n_g - n'_g | dnu.

Including the direct repair edges T_s on Y \ E_s in the multiplicities only
increases d, so every lower bound below holds for that variant too. Comparing
domains of copies, used or not, would be the wrong notion: on the example of
Section 3, keeping every edge copy of D and routing nothing gives a plan with
zero domain distance, B = r = 1 and J = 0, which has only moved the whole
budget onto direct repairs. The used-edge change is what a removal pays.

The two elementary facts used repeatedly are

    1_{N_j >= 1} <= n_{g_j},   hence  O_j <= E[n_{g_j} | pi];              (1.1)
    integral | E[n'_g | pi] - E[n_g | pi] | dmu <= integral |n'_g - n_g| dnu. (1.2)

(1.2) is the L1 contraction of conditional expectation.

## 2. Small defect puts reuse on high-occupancy edges (any group, any factor)

**Lemma 2.1.** Let D be any finite routing plan over a free factor pi of any
countable group, and let 0 < c < 1. For each copy j put

    W_j = { x in X : a_j(x) >= c and b_j(x) < c }.

Call an occurrence (j, z) with N_j(z) >= 1 *light* if pi(z) lies in W_j, and
*heavy* otherwise. Then

    (i)   sum_j integral_{pi^{-1} W_j} (N_j - 1)_+ dnu  <=  J_pi(D);
    (ii)  the heavy occurrences have total measure
          eta <= sum_j integral_{ {a_j < c} } O_j dmu  +  J_pi(D)/c;
    (iii) sum_j integral_{pi^{-1} W_j} N_j dnu <= (B - r) + J_pi(D).

*Proof.* On W_j we have b_j < c <= a_j, so min(a_j, b_j) = b_j there, and the
integral over pi^{-1} W_j of (N_j - 1)_+ equals the integral of b_j over W_j.
Summing gives (i). A heavy occurrence of copy j lies over {a_j < c} or over
V_j = {a_j >= c, b_j >= c}. The first part has measure equal to the integral
over {a_j < c} of O_j. The second has measure at most mu(V_j), and
min(a_j, b_j) >= c on V_j, so sum_j mu(V_j) <= J/c. This is (ii). For (iii)
write N_j = 1_{N_j >= 1} + (N_j - 1)_+, bound the first term by
sum_j nu(N_j >= 1) = B - r and the second by (i). QED.

Reading: a plan of small defect does all but J of its repeated use on copies
whose occupancy given the base exceeds 1 - c, that is on edges nearly
determined by the base point, or over base regions of total measure J/c.
Nothing about sparsity or entropy of flags is assumed.

**Lemma 2.2 (occupancy is stable under small edits).** Let D, D' be plans
with used-edge multiplicities n_g, n'_g, and suppose a label g satisfies
E[n_g | pi] <= 1/2 mu-almost everywhere. Then for 0 < c < 1/2,

    sum_{j : g'_j = g} integral_{ {a'_j < c} } O'_j dmu
        <=  ( 1/(1 - 2c) + 1 ) integral |n'_g - n_g| dnu.

If n_g = 0 identically, the left side is at most integral n'_g dnu, which
equals integral |n'_g - n_g| dnu.

*Proof.* Put e = |E[n'_g - n_g | pi]|. By (1.1), a'_j < c forces
E[n'_g | pi] > 1 - c, hence e > 1/2 - c, for every copy j of label g. Let F
be the set {e > 1/2 - c}. By (1.1) summed over copies of label g (their
indicators add up to at most n'_g) and by (1.2),

    sum_j integral_{ {a'_j < c} } O'_j <= integral_F E[n'_g | pi] dmu
                                         <= mu(F)/2 + integral e dmu,

and Markov's inequality gives mu(F) <= integral e / (1/2 - c). The case
n_g = 0 is (1.1) integrated. QED.

## 3. The parity plan on a fixed free factor of Z

Let X = {0,1}^Z with the fair Bernoulli shift sigma, Y = X x Z/2 with
T(x, i) = (sigma x, i + 1), and pi(x, i) = x. Both actions are free (a nonzero
power of sigma has a null fixed set), and both have cost exactly one: the full
generator graphing costs one and every aperiodic p.m.p. relation has cost at
least one. There is one request, S = {1}, y -> Ty. Write P_0 = {i = 0} and
P_1 = {i = 1}; these are independent of the base, so P(P_0 | pi) = 1/2.

**The plan D.** Label +2 on P_0, label +3 on P_1. Paths:

    y in P_0:   y --(+2 at y)--> T^2 y --(+2 at T^2 y)--> T^4 y <--(+3 at Ty)-- Ty,
    y in P_1:   y --(+3 at y)--> T^3 y <--(+2 at Ty)-- Ty.

Every step uses an existing copy: T^2 y is in P_0 when y is, Ty is in P_1
when y is in P_0 and in P_0 when y is in P_1. Paths have length at most 3,
so D is a finite routing plan, and every request is covered (r = 0).

**Traffic.** A +2 copy at z in P_0 is used by the requests of z (first step),
of T^{-2} z (second step) and of T^{-1} z, which is in P_1 (reversed step):
N = 3. A +3 copy at z in P_1 is used by the requests of T^{-1} z in P_0
(reversed third step) and of z: N = 2. Hence B(D) = nu(P_0) + nu(P_1) = 1 and

    a_{+2} = a_{+3} = 1/2,   b_{+2} = 2 * 1/2 = 1,   b_{+3} = 1 * 1/2 = 1/2,
    J_pi(D) = 1/2 + 1/2 = 1.

So D is exactly optimal for the source, has defect one although C(X) = C(Y),
and its used-edge multiplicities are n_{+2} = 1_{P_0}, n_{+3} = 1_{P_1},
n_g = 0 for all other g, with E[n_{+2} | pi] = E[n_{+3} | pi] = 1/2.
Its reuse flags 1_{N_j >= 2} are 1_{P_0} and 1_{P_1}: they generate the whole
extension, so the compression factor of Theorem 4.1 of the compression artifact
is Y itself. The verifier replays these paths and counts in exact arithmetic.

**Theorem 3.1.** Every finite routing plan D' for the same factor and request
with B(D') <= 1 + beta and J_pi(D') <= delta satisfies

    d(D, D') >= (1 - 2 beta - 81 delta) / 65.

In particular there are no plans D'_n with d(D, D'_n) -> 0, B(D'_n) -> 1 and
J_pi(D'_n) -> 0, although plans with B = 1 and J = 0 exist (the direct
generator plan, at distance 2 from D).

*Proof.* Let d = d(D, D') and d_g = integral |n'_g - n_g|, so sum_g d_g = d.
Take c = 1/4 in Lemma 2.1 applied to D', with W_j, light and heavy
occurrences as there; write u(y) for the number of light occurrences on the
path of a covered request y.

*Step 1: heavy measure.* Lemma 2.2 with c = 1/4 gives, for g = +2 and g = +3,
the bound 3 d_g, and for every other label the bound d_g. With Lemma 2.1(ii),

    eta <= 3d + 4 delta.                                                   (3.1)

*Step 2: light traffic.* The traffic identity (1) of the compression artifact,
applied with h_j = 1_{W_j} o pi, and Lemma 2.1(iii) give

    integral_E u dnu = sum_j integral_{pi^{-1} W_j} N'_j dnu <= (B' - r') + delta.   (3.2)

*Step 3: most requests need two light steps.* Let y be covered with u(y) <= 1
and path y = v_0, v_1, ..., v_k = Ty, k >= 1. One of three things holds.

(a) The first step is heavy. Then y is an endpoint of a heavy occurrence. The
starts of heavy occurrences have measure eta and T^{g_j} preserves measure, so
these y have measure at most 2 eta.

(b) The first step is light with label not in {+2, +3}. Then y is the start or
the end of a used copy with such a label; measure at most
2 sum_{g not in {2,3}} integral n'_g <= 2d, because n_g = 0 for those labels.

(c) The first step is light with label +2 or +3 (forward or reversed). A single
step moves by +-2 or +-3, never by +1, so k >= 2, and since u(y) <= 1 the
second step is heavy. Then v_1 = T^t y with t in {2, -2, 3, -3} is an endpoint
of a heavy occurrence: measure at most 4 * 2 eta.

Hence nu({y in E : u(y) <= 1}) <= 10 eta + 2d and

    integral_E u dnu >= 2 ( 1 - r' - 10 eta - 2d ).                         (3.3)

*Step 4: budget.* Since the used multiplicities of D integrate to one,
sum_g integral n'_g >= 1 - d, so r' = B' - sum_g integral n'_g <= beta + d, and
B' - r' <= 1 + beta - r'. Combining (3.2) and (3.3),

    2 - 2r' - 20 eta - 4d <= 1 + beta - r' + delta,
    1 <= r' + 20 eta + 4d + beta + delta
      <= (beta + d) + 20(3d + 4 delta) + 4d + beta + delta = 65 d + 2 beta + 81 delta.

QED.

**Corollary 3.2 (an open set of bad optimal-ish plans).** If d(D, D'') <= epsilon_0
then every plan D' with B(D') <= 1 + beta and J(D') <= delta has
d(D'', D') >= (1 - 2 beta - 81 delta)/65 - epsilon_0, by the triangle inequality.
Such D'' have used budget at most 1 + epsilon_0, and those with small
uncovered mass r'' are source-near-optimal. So a whole L1-ball of
source-near-optimal plans admits no perturbative removal.

## 4. What is killed, and at which step every member dies

**The class.** Call a removal statement *perturbative* if it has the form: for
a free factor pi (of a given group, or of all groups) and for every sequence
of source plans D_n with B(D_n) -> C(Y), there are plans D'_n with
d(D_n, D'_n) -> 0, B(D'_n) -> C(Y) and J_pi(D'_n) -> 0. This covers every
procedure that repairs a given near-optimal source plan by edits of vanishing
measure: deleting or re-routing flags on sparse sets, sparse sprinkling or
rare repair edges added to the given plan, local recoding of reuse flags on
small regions, and their combinations, whatever their rules are.

**It is false**, already for Z and one fixed factor where both costs equal one
(Theorem 3.1 with D_n = D). Hence no perturbative statement can serve as a
universal removal theorem, and none can serve for any family of groups or
factor maps that contains this Z factor. A per-plan removal theorem of form
(I) must allow edits of measure bounded below by a positive constant times the
budget: at least (1 - 2 beta - 81 delta)/65 on this example, where some
correct plan lies at distance 2.

**The invariant** is the base-conditional occupancy E[n_g | pi] of each label.
Small edits move it only in L1 (Lemma 2.2). **The step where every member
dies** is Lemma 2.1: a small defect forces repeated traffic onto copies of
occupancy above 1 - c or onto rare base regions. A source plan whose budget
sits on noise-split labels (occupancy 1/2) has no such copies, so after a
small edit all but O(d + delta) of its reuse must be single use. On Z each
request whose path avoids the O(d + delta) heavy set needs at least two light
steps (no used label equals the request), while single-use light edges supply
at most one unit of traffic per unit budget; this contradicts optimal budget.

**What survives.**

* Cost preservation for this factor is true (Z has fixed price), witnessed
  by a plan far from D. Nothing here is a counterexample to the target claim or
  to Fixed Price; the target claim stays OPEN.
* Form (I) with macroscopic edits (a global rebuild whose cost is explicitly
  bounded but not small) is untouched, and so is form (II) where the new
  plans are not derived from arbitrary given plans.
* Theorem 4.1 of the compression artifact is consistent with this: on D its
  intermediate factor is Y itself, so compression does not help either.

**Diagnostic for other attempts.** Any proposed removal procedure that, applied
to a given plan, changes a vanishing measure of used edges must fail on D.
Before building such a procedure, test it on D: it must change at least a
fixed fraction of the budget there. The sparse-sprinkling and rare-repair
ideas recorded under the target's Attempts were aimed at chosen plans or
chosen helpers; this note shows they cannot be upgraded to act on arbitrary
source-near-optimal plans with vanishing edit cost.

## 5. Scope and possible extensions

* The counting of Step 3 uses Z: steps of +-2 and +-3 never equal the request.
  For a general finitely generated group the analogous plan needs a
  near-optimal source plan whose macroscopic budget sits on labels split by
  independent noise while every request still needs two light steps. Lemma
  2.1 and Lemma 2.2 are group-free and apply as they stand; the group-specific
  part is only the analogue of Step 3. Whether perturbative removal fails for
  every infinite finitely generated group, and hence for every restricted
  family, is not proved here.
* The constants 65 and 81 are not optimised. Varying c trades them against
  each other.
* Related established claims: `fpbs-binary-entropy-traffic-tail-bound`
  (specified plans with vanishing flag entropy but J = 1 on an odometer
  factor; its budget sits on labels of occupancy 1 - 1/q and 1/q, which tend
  to 0 or 1, so Lemma 2.2 gives no obstruction there and no distance bound is
  claimed for those plans) and `fpbs-cost-one-plans-have-heavy-traffic-tails`
  (congestion lower bounds for nonamenable groups; it concerns traffic tails,
  not distance to small-defect plans).

## References

* Compression artifact: `research/artifacts/fpbs/docs/fixed-price-reuse-compression.md`,
  Sections 1--4 (plans, traffic identity (1), defect (4), overlap form (9)).
* `fpbs-traffic-defect-is-total-variation-loss` (formula (9)).
* Cost of aperiodic relations is at least one and the full generator graphing
  of Z costs one: Gaboriau, *What is... cost?*, https://arxiv.org/pdf/1011.2294
  (background; the fact is also used in `fpbs-binary-entropy-traffic-tail-bound`).
* Verifier: `experiments/fpbs-perturbative-reuse-removal-2026-09-17/parity_plan_verifier.py`.
