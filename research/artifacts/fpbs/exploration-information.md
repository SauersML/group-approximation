# Information cost of connection exploration near criticality

Date: 2026-09-10. This develops an algorithmic route to the full
Benjamini--Schramm goal. It proves necessary query-cost bounds under
uniqueness, not uniqueness's impossibility. No matching algorithmic
upper bound or claim of mathematical priority is supplied.

## 1. Adaptive transcripts retain an exact product-law identity

Let 0<c<q<1. An algorithm has a parameter-independent random seed,
adaptively queries previously unobserved edges, and halts after N queries.
Its decisions use only the seed and the already observed answers. Assume
it halts almost surely under both Bernoulli-c and Bernoulli-q laws.
The seed may include a random-walk endpoint; the algorithm may be chosen
using the numbers c,q, provided the SAME algorithm is run under both laws.
Let Z be its terminal transcript, including its seed, queries, answers,
and output. Write

    k(q,c)=q log(q/c)+(1-q) log((1-q)/(1-c)).

**Lemma 1.** In the extended nonnegative reals,

    D(Law_q(Z) || Law_c(Z)) = k(q,c) E_q N.                (1)

If its output is a bit of respective probabilities b_q,b_c, then

    d(b_q,b_c) <= k(q,c) E_q N,                           (2)

where d is binary relative entropy.

**Proof.** Conditional on any history at which a fresh edge is requested,
that edge still has the original Bernoulli law. For a finite transcript
with u open and v closed answers its likelihood ratio is
(q/c)^u ((1-q)/(1-c))^v. The seed and adaptive choices contribute no
additional likelihood ratio. The chain rule for a transcript capped
after M queries therefore gives entropy k(q,c) E_q[min(N,M)].

For completeness, extend the observation sequence by a deterministic
stopped symbol after halting. Its increasing prefix sigma-fields
generate the terminal transcript, since halting occurs almost surely
under both laws. Relative entropy increases to the entropy on their
union: this follows from the variational formula
D(P||Q)=sup_f(E_P f-log E_Q exp(f)) for bounded measurable f, approximating
bounded f by prefix-measurable conditional expectations under (P+Q)/2.
This also handles infinite expected query count. Let M increase to infinity
and use monotone convergence. Finally group terminal transcripts by their
output bit. The log-sum inequality, equivalently convexity of t log t,
says this grouping cannot increase entropy, proving (2). QED.

The algorithm must not receive unqueried percolation information as part
of its seed. In particular, the two laws cannot be assigned different
search rules during this comparison.

## 2. Critical spectral decay forces query expenditure under uniqueness

Fix the original nonamenable d-regular Cayley graph. Let c=p_c,
rho<1 be the norm of its lazy walk, lambda=-log rho, and X_n its
independent endpoint. Write a_n(p)=P_p(o connected to X_n).

The established critical correlation bound gives a_n(c)<=rho^n.
If q>c is a uniqueness parameter, a_n(q)>=theta(q)^2 by positive
association. An exact, almost surely halting connection algorithm under
both c and q therefore satisfies

    E_q N_n >= [theta(q)^2 lambda n-log 2]/k(q,c).          (3)

Indeed d(a,b)>=a log(1/b)-h(a), where h is binary entropy and h(a)<=log 2.
Apply Lemma 1, then the two connection bounds. A negative right side in
(3) is harmless. No differentiation in p or uniform finite-ball limit
is involved.

## 3. Balanced two-ended search isolates the infinite-cluster cost

Consider the following class of connection algorithms. Grow the discovered
open components from both endpoints, caching every queried edge globally.
Alternate which side makes the next fresh query. Each side uses a schedule
that eventually processes every edge incident to its discovered component
if the search continues forever; breadth-first order is one example.
Reading a cached answer costs no fresh query. Stop successfully when the
discovered sets meet; stop unsuccessfully when one side's frontier is
exhausted. For coincident endpoints stop immediately.

Such an algorithm halts if either endpoint has a finite cluster, or if
the endpoints are connected. In the connected case a finite connecting
path is eventually explored by the exhaustive schedules. Consequently it
halts almost surely both at c and at a uniqueness parameter q>c.
We do not assert that it halts on two distinct infinite clusters.

Here is a concrete target-directed schedule within the class. When a side
first discovers a vertex u, give u its depth in that side's discovery
tree. Queue each incident oriented edge (u,v) with priority

    depth(u)+1+beta distance_G(v,other endpoint), beta>=0. (3a)

Process the smallest priority first, breaking ties deterministically.
This uses only the known ambient graph and revealed answers. The
discovery depth is fixed at first discovery; optimal open distances are
not required. For each finite K, candidates of priority at most K have
discovery-tree depth at most K and there can be only finitely many on a
bounded-degree graph. Hence every queued edge is eventually processed
if the algorithm continues. This proves exhaustiveness for every fixed
finite beta, including beta=0 (breadth-first), 1, and 2 used in the replay.
It proves correctness and eventual termination in the stated regimes,
not an expected-query upper bound. Ambient distance is deterministic
geometry in this query model, not unqueried percolation information.

If C_x is finite, that side can make at most d|C_x| fresh queries. Balanced
alternation and the exhaustion stopping rule imply the pathwise bound

    N_n <= 2d |C_x|+1                                   (4)

whenever either endpoint x has a finite cluster. This bound concerns fresh
queries, even if the other side also reads cached answers.

We explicitly import Hermon--Hutchcroft, arXiv:1904.10448v3, Theorem 1.1:
finite clusters have exponential tails at every fixed q>p_c on a
nonamenable transitive graph. In particular

    chi_fin(q)=E_q[|C_o|; |C_o|<infinity] < infinity.       (5)

Let I_n be the event that both endpoint clusters are infinite. Transitivity,
independence of X_n from percolation, and (4) give

    E_q[N_n; I_n^c] <= 4d chi_fin(q)+1.                  (6)

The centered infinite-cluster indicator is a mean-zero Bernoulli factor.
The existing lazy covariance bound gives, for every fixed q,

    P_q(I_n)=theta(q)^2+b_n(q),
    0<=b_n(q)<=theta(q)(1-theta(q))rho^n.                 (7)

**Theorem 2.** For any balanced exhaustive two-ended search and any
uniqueness parameter c<q<1,

    liminf_{n->infinity} E_q[N_n | I_n]/n
      >= lambda/k(q,c).                                 (8)

The conditional expectations may be infinite.

**Proof.** Subtract (6) from (3), write
E_q[N_n;I_n]=P_q(I_n)E_q[N_n|I_n], and use (7). For fixed q,
chi_fin(q) and k(q,c)>0 are constants and theta(q)>0. Dividing by n
and letting n increase proves (8), including the infinite-cost case.
QED. We do not require a bound uniform in q for chi_fin(q).

Thus the cost forced by the entropy comparison persists after removing
all cases with a finite endpoint cluster. It is not an artifact of the
infinite susceptibility of critical clusters.

## 4. The quadratic scale and what would complete this route

Put B_A(q)=liminf_n E_q[N_n|I_n]/n for a chosen family of balanced,
exhaustive algorithms A (their schedules may depend on q and n).
Taylor's theorem gives

    k(c+epsilon,c)=epsilon^2/[2c(1-c)]+O(epsilon^3).

If uniqueness parameters q_j decrease to c, then for ANY such algorithm
family

    liminf_j (q_j-c)^2 B_A(q_j)
      >= 2c(1-c)lambda > 0.                             (9)

In particular threshold collapse would force (9) along every sequence
q_j down to c. A construction, made under the collapse assumption,
with conditional query rate strictly below this constant along one
sequence would contradict collapse and prove the requested interval.
An o((q-c)^(-2)) rate would suffice. No such construction is established
here; inequality (9) is a necessary condition, not a contradiction.

The search schedule is the substantive missing issue. Breadth-first
search can expose exponentially many vertices on an exponentially growing
graph, so the finite replay below supplies no efficient-search upper bound.
Positive anchored expansion and finite-cluster exponential tails alone
do not give that bound in this argument. Nor may shortest-path length be
substituted for query count: finding a path can require many queries
outside the path eventually returned.

This route differs from counting pivotal edges: it controls all observed
edges through the exact likelihood of the exploration transcript. The
next task is a target-directed, exhaustive search with a proved query
bound under hypothetical uniqueness, or an obstruction showing why that
strategy cannot achieve the strict inequality. The full every-Cayley-graph
quantifier is unchanged.

## 5. Sources and verification scope

The critical correlation, critical finiteness, positive-association and
Bernoulli covariance inputs are already recorded in `spectral-spike.md`
and `fpbs-critical-walk-correlation`. The additional published input (5)
is Hermon--Hutchcroft, *Supercritical percolation on nonamenable graphs:
Isoperimetry, analyticity, and exponential decay of the cluster size
distribution*, [Theorem 1.1](https://arxiv.org/pdf/1904.10448), v3.
We use its fixed-parameter conclusion only, not a near-critical exponent.
The transcript proof is the standard sequential relative-entropy
calculation supplied here in the required stopped-query form.

`scripts/replay_exploration_information.py` checks finite graph reachability,
the balanced stopping bound, exact terminal-cylinder probabilities,
likelihood ratios, and the exact identities E_p(open queries)=p E_p N.
The replay includes the target-directed schedule (3a) for beta=0,1,2.
All 288 cases passed on MSI, covering 7,344 edge configurations and
2,918 terminal transcripts with exact rational arithmetic. Its output is
`exploration-information-replay.json`. Cairn validation is recorded in
`exploration-information-validation.json`. These checks do not formally
verify the infinite theorems or supply the missing algorithmic upper bound.
