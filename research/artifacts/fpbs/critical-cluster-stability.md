# Critical cluster stability and continuity of the finite spectral contribution

Date: 2026-09-09. Status: written proofs, not Lean verification. Neither
Benjamini--Schramm nor a new universal percolation estimate is proved here.
No novelty claim is made. This note strengthens the finite-cluster part of
`spectral-spike.md` and specifies why this still leaves its obstruction open.

## 1. Coupling and the exact stability probability

Fix a locally finite nonamenable Cayley graph, with degree d, critical
parameter c, and independent uniform edge labels U_e. Edges with U_e <= p
are open at p. Let C_p(v) be the resulting cluster. We use the published
critical-finiteness theorem, so C_c(v) is finite almost surely. Write

    B = |boundary_E C_c(o)|,
    t = (q-c)/(1-c),                     c <= q < 1,
    delta(q) = P(C_q(o) != C_c(o)).

Here boundary_E counts edges with precisely one endpoint in the cluster.
Then

    delta(q) = E[1-(1-t)^B].                              (1)

To prove (1), condition on C_c(o)=K, for each possible finite connected K.
This event is the intersection of an internal connectivity event and the
event that every boundary edge has label greater than c. These involve
disjoint edge sets. Conditional on this event, the boundary labels remain
independent uniforms on (c,1). The cluster stays exactly K at q if and only
if none of those labels is at most q. Summing over K proves the identity.

In particular delta(q) tends to zero as q decreases to c, by dominated
convergence; no finite expected cluster size is required. For any positive
integer M,

    delta(q) <= t M + P(B > M),
    delta(q) = t sum_{k>=0} (1-t)^k P(B > k).               (2)

The first bound uses 1-(1-t)^B <= min(tB,1). For the second use the finite
geometric series for each finite B and Tonelli. The formula at t=0 is
understood separately as delta(c)=0.

Also theta(q) <= delta(q): an infinite q-cluster cannot equal a finite
c-cluster. This elementary bound will matter when assessing the limitation.

## 2. One spectral operator for all parameters

Let P be the lazy simple random-walk operator and rho=||P||<1. Let X_n be
the walk, independent of all labels, and put

    a_n(p) = P(o connected to X_n at p),
    f_n(p) = P(o connected to X_n at p, |C_p(o)| < infinity).

Use a single collection of independent vertex priorities and fair signs
at every parameter, independent of the edge labels. For a finite C_p(v),
let F_p(v) be the sign at its least-priority vertex; for an infinite
C_p(v), let F_p(v)=0. This is measurable and equivariant, and has mean
zero. All these random variables live on the same Bernoulli probability
space. The half-edge construction in `spectral-spike.md`, Section 2,
realizes edge labels there even for involutory generators.

Let M be the lazy Koopman walk operator on its mean-zero L2 space. The
Bernoulli covariance lemma gives spectrum(M) contained in [0,rho]. This
is the SAME operator at c and q; only its vectors F_c(o), F_q(o) change.
Conditional sign averaging gives

    f_n(p) = <F_p(o), M^n F_p(o)>,
    ||F_p(o)||_2^2 = 1-theta(p).                           (3)

On the event that C_q(o)=C_c(o), the two selected signs agree. Conditional
on the clusters and priorities, their squared difference has expectation
zero if the selected vertex is the same, two if both clusters are finite
and the selected vertices differ, and one if C_q(o) is infinite. Therefore

    ||F_q(o)-F_c(o)||_2^2 <= 2 delta(q)-theta(q).            (4)

This uses critical finiteness and the fact that the infinite-cluster event
is a subset of the changed-cluster event. In particular the right side is
nonnegative.

## 3. Total variation and uniform normalized continuity

Let mu_p be the scalar spectral measure of F_p(o) for M. It is supported
in [0,rho], has mass 1-theta(p), and has moments f_n(p). Use the total
variation norm of a signed measure (with no factor one half), and set

    K(q) = (1 + sqrt(1-theta(q))) sqrt(2 delta(q)-theta(q)).

Then

    ||mu_q-mu_c||_TV <= K(q) <= 2 sqrt(2 delta(q)),          (5)
    sup_{n>=0} rho^(-n) |f_n(q)-a_n(c)| <= K(q).            (6)

Indeed, for every real bounded Borel function h on [0,rho] with |h|<=1,
the spectral calculus gives ||h(M)||<=1. Writing u=F_q(o), v=F_c(o),

    |<u,h(M)u>-<v,h(M)v>|
      <= ||u-v|| (||u||+||v||).

Equations (3)-(4), theta(c)=0, and the dual characterization of total
variation prove (5). Apply the same estimate to h(s)=(s/rho)^n to get
(6), using f_n(c)=a_n(c). Both right sides tend to zero as q decreases
to c. This is stronger than continuity for each fixed n, but applies to
FINITE-cluster contributions only.

## 4. What uniqueness would have to add

Suppose there is a unique infinite cluster at q. Center its membership
indicator and call its scalar spectral measure beta_q. The existing
uniqueness decomposition gives

    a_n(q) = theta(q)^2 + integral s^n d nu_q(s),
    nu_q = mu_q + beta_q,
    supp(beta_q) subset [0,rho],
    beta_q([0,rho]) = theta(q)(1-theta(q)).

Thus (5) gives

    ||nu_q-mu_c||_TV <= K(q)+theta(q)(1-theta(q)),           (7)
    |a_n(q)-theta(q)^2-a_n(c)|
      <= [K(q)+theta(q)(1-theta(q))] rho^n.                 (8)

This estimates the remainder uniformly in n along ANY sequence of
uniqueness parameters decreasing to c, if such a sequence exists. It
does not assert that there is such a sequence.

In particular, collapse would be compatible with total variation
convergence of the spectral measure

    theta(q)^2 Dirac_1 + nu_q  -->  mu_c.

The total variation distance is at most
theta(q)^2+K(q)+theta(q)(1-theta(q)), which tends to zero because
theta(q)<=delta(q). Nevertheless its upper support point is 1 at every
uniqueness parameter with theta(q)>0, whereas mu_c is supported below 1.
Total variation convergence does not control that upper support point.

## 5. A finite exact control demonstrating the limitation

Fix 0<rho<1 and 0<s<1. The probability measures

    eta_0 = Dirac_rho,
    eta_s = s^2 Dirac_1 + (1-s^2) Dirac_rho

satisfy ||eta_s-eta_0||_TV=2s^2, with moments

    m_n(s) = s^2 + (1-s^2)rho^n.

For every s>0 their n-th-root moment limit is 1; at s=0 it is rho.
Moreover

    sup_n rho^(-n)|m_n(s)-s^2-m_n(0)| = s^2.

So even the strengthened normalized remainder control has no implication
of continuity of the full exponential rate. These two-atom measures are
a control for that inference, NOT a Bernoulli percolation construction,
and NOT a counterexample to Benjamini--Schramm. The earlier FIID partition
example remains subject to its explicit disconnected-class limitation.

The universal gap is still an estimate that prevents or controls the
infinite-cluster term immediately above c. Neither (1), (5), nor (8)
does that. In particular replacing the OPEN integrated-sensitivity
hypothesis by (6) would incorrectly replace full connectivity by finite
connectivity.

## 6. Validation and sources

`scripts/replay_critical_cluster_stability.py` exhaustively enumerates
three-state edge configurations on three small graphs and verifies (1)
as a rational polynomial identity at specified rational parameters. It
also checks (4) by enumerating priority orders for all nested partitions
of four vertices, and checks the two-atom formulas exactly. These tests
do not verify the infinite spectral or percolation theorems. They run
only on MSI. Cairn checks the dependency graph, not the proof text.

Critical finiteness is the theorem of Benjamini--Lyons--Peres--Schramm;
a recent exposition is Tasmin Chu, *Applications of the cluster graphing*,
Theorem 1.1, https://arxiv.org/abs/2608.06644.
The local proof of the Bernoulli representation bound and uniqueness
decomposition is in `spectral-spike.md`, Sections 2-4. Its spectral
calculus concerns the bounded Koopman walk operator, not the possibly
unbounded connectivity convolution operator.
