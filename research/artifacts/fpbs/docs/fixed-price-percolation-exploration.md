# Exploration: pivotal concentration, collective fragility, and critical cluster projections

Date: 2026-09-08 (America/Chicago).

## Status and scope

This continuation proves several restricted statements and conditional reductions. It does not prove or refute the universal Fixed Price or Benjamini–Schramm conjectures. No claim of priority is made for the results derived here. The hypotheses concerning every nonamenable Cayley graph remain OPEN. The numerical work is finite algebra and evaluation of explicit formulas, not a verification of infinite-volume theorems.

The focus is Bernoulli bond percolation on locally finite Cayley graphs. Counterexamples below concern explicitly different, dependent or anisotropic laws; they are not counterexamples to the Bernoulli conjecture. Invariant and factor-of-iid (FIID) mean invariant/equivariant under the group action, not necessarily under every automorphism of the underlying unlabelled graph.

The investigation has four outcomes:

1. The previous no-bridge graph can nevertheless be destroyed by thinning of arbitrarily small density, as its sparsity parameter tends to zero.
2. The pivotal-budget route can be weakened to an integrated non-concentration criterion. A collapsed threshold window would concentrate an explicitly determined normalized sensitivity at criticality.
3. The proposed dyadic cluster-projection estimate is proved, with sharp exponent 3/2, on every regular tree of degree at least three.
4. On a fixed nonamenable Cayley graph there is an FIID finite-cluster process for which the dyadic summability estimate fails. Nonamenability, equivariance, FIID admissibility, and critical-style infinite susceptibility are therefore not enough on their own.

## 1. No bridges does not imply resilience to collective deletion

Let G = T_(2r) square Z, r >= 2. Let H_epsilon retain every vertical edge and retain each horizontal edge independently with probability epsilon > 0.

Almost surely H_epsilon is connected: neighboring vertical fibers have infinitely many independent opportunities for a horizontal crossing, so each neighboring pair has a crossing. Every edge lies in a finite rectangle. For a horizontal edge, use another crossing between the same fibers at a different height. For a vertical edge, use crossings to a neighboring fiber both above and below the edge. These assertions hold simultaneously by countability. Consequently, H_epsilon has no bridges and no single-edge pivotal for connectivity of any pair.

Now independently retain each edge of H_epsilon with probability q < 1. Averaging over both stages gives independent anisotropic Bernoulli percolation on the ambient graph, with vertical retention q and horizontal retention epsilon q.

### Proposition 1: a susceptibility and thinning bound

Put

    chi_v(q) = (1+q)/(1-q),
    alpha = 2r epsilon.

If

    alpha q chi_v(q) < 1,                                      (1.1)

then

    E |C(o)| <= chi_v(q) / [1 - alpha q chi_v(q)] < infinity.   (1.2)

In particular, for almost every H_epsilon, its bond threshold is at least

    q_0(epsilon,r)
      = 2 / [1 + alpha + sqrt((1+alpha)^2 + 4 alpha)].           (1.3)

Thus

    p_c(H_epsilon) >= q_0(epsilon,r)
                    = 1 - 4r epsilon + O_r(epsilon^2),

and p_c(H_epsilon) tends to one as epsilon decreases to zero.

#### Proof

Any simple open path decomposes into vertical segments separated by horizontal steps. The sum of the weights q^|k| of all possible vertical displacements is chi_v(q). At a horizontal step there are 2r choices, each with weight epsilon q.

The probability of a particular simple path being open is the product of these weights, since its edges are distinct. A union bound over simple paths is at most the sum over all alternating sequences of vertical segments and horizontal steps. The latter sum equals

    sum_(m>=0) chi_v(q)^(m+1) (2r epsilon q)^m.

This geometric series gives (1.2). Non-simple sequences are only extra positive terms in the upper bound; their product weights are not claimed to be their open-event probabilities.

Finite expected cluster size rules out an infinite root cluster. Countability rules out any infinite cluster. For each rational q satisfying (1.1), Fubini's theorem implies that, for almost every realization H_epsilon, q-percolation on H_epsilon has no infinite clusters. Intersect over the countably many such rationals and use monotonicity. The positive root of alpha q(1+q)=1-q is (1.3). Expansion at alpha=0 proves the final assertion. QED.

For r=2 the bounds are:

| epsilon | rigorous lower bound on p_c(H_epsilon) |
|---:|---:|
| 0.01 | 0.9283882772 |
| 0.003 | 0.9768277573 |
| 0.001 | 0.9920946146 |

These are lower bounds, not claimed exact thresholds. The example does not disprove the earlier pivotal-budget hypothesis for ordinary Bernoulli percolation. It shows why zero single-edge influence at one law cannot substitute for an integrated near-critical sensitivity estimate.

## 2. Replace a pointwise pivotal budget by a non-concentration criterion

Let G be a nonamenable Cayley graph, let c=p_c(G), and let X_n be the lazy simple random walk with holding probability 1/2, independent of percolation. Write rho<1 for this lazy walk's l2 spectral radius.

Define

    a_n(p) = P_p(o connected to X_n).

Schramm's lemma gives a_n(c) <= rho^n [H1, Proposition 6.4]. The lazy version follows by averaging the simple-walk inequality over a binomial number of actual steps. Also a_n(c) >= P(X_n=o), so the standard return-probability spectral-radius formula gives

    lim_(n->infinity) (1/n) log a_n(c) = log rho.                (2.1)

The same limit holds with a_n replaced by any finite-volume a_(n,R_n), provided R_n>=n, because the same upper bound and return-probability lower bound apply.

For R>=n let E_(n,R) be connection from o to X_n inside the induced ball B_R, and set a_(n,R)(p)=P_p(E_(n,R)). Let N_(n,R)(p) be the number of open edges pivotal for this connection on E_(n,R). All expectations include the independent random walk.

Finite-volume Russo differentiation yields

    d/dp log a_(n,R)(p)
      = E_p[N_(n,R)(p) | E_(n,R)] / p.                         (2.2)

One conditions first on X_n and differentiates its finite connection event. The pivot event does not depend on the tested edge's own state, and an open pivotal edge implies the increasing connection event. This gives (2.2) after averaging and division. See [J] for the same finite two-point differentiation mechanism.

For c<t<=1 define the normalized integrated budget

    M_(n,R)(t)
      = (1/n) integral_c^t E_p[N_(n,R)(p)|E_(n,R)] dp/p
      = (1/n) log[a_(n,R)(t)/a_(n,R)(c)].                      (2.3)

This is a finite-polynomial identity before integration; it makes no assertion about differentiating an infinite-volume event.

### Proposition 2: the total normalized budget is already controlled

For every n and R>=n,

    0 <= M_(n,R)(1) <= log(1/c).                               (2.4)

More precisely, for every sequence R_n>=n,

    lim_(n->infinity) M_(n,R_n)(1) = -log rho.                 (2.5)

#### Proof

At parameter one, B_R is connected and contains X_n, so a_(n,R)(1)=1. For every possible endpoint of X_n, a path of length at most n inside B_n exists, so a_(n,R)(c)>=c^n. This proves (2.4). The squeeze leading to (2.1) then proves (2.5). QED.

Thus proving only an O(n) total pivotal budget over the entire parameter interval would add nothing here. The location of the budget is the issue.

### Proposition 3: a weaker sufficient criterion for nonuniqueness

For 0<epsilon<1-c define

    B(epsilon) = limsup_(n->infinity) lim_(R->infinity)
                   M_(n,R)(c+epsilon).                       (2.6)

The inner limit exists by (2.3) and monotone finite-volume approximation of the two connection probabilities. If, for some epsilon,

    B(epsilon) < -log rho,                                   (2.7)

then G has a nonuniqueness interval. More precisely, a_n(c+epsilon) decays exponentially in n, and every p in (c,c+epsilon] has infinitely many infinite clusters almost surely.

#### Proof

Passing R to infinity in (2.3) and using (2.1) gives

    limsup_n (1/n)log a_n(c+epsilon)
       = log rho + B(epsilon) < 0.

Uniqueness at a supercritical p would imply

    P_p(x connected to y) >= theta(p)^2 > 0

for all x,y by positive association, contradicting a_n(p) tending to zero. Monotonicity a_n(p)<=a_n(c+epsilon) gives the same exclusion of uniqueness throughout (c,c+epsilon]. The standard transitive Bernoulli cluster-number and threshold theorems give infinitely many infinite clusters there. These are the same percolation phase facts used in [H2, Section 1]. QED.

The stronger condition

    lim_(epsilon->0) B(epsilon)=0                             (2.8)

would of course suffice. The earlier pointwise bound E[N|E]<=Cn implies (2.8), because it gives B(epsilon)<=C log(1+epsilon/c). The integrated criterion allows large narrow peaks that a pointwise bound excludes.

### Proposition 4: a collapsed window forces a critical sensitivity concentration

If p_c(G)=p_u(G)=c, then for every fixed epsilon in (0,1-c),

    lim_(n->infinity) lim_(R->infinity)
       M_(n,R)(c+epsilon) = -log rho.                         (2.9)

At each fixed n, however,

    lim_(epsilon->0) lim_(R->infinity)
       M_(n,R)(c+epsilon) = 0.                               (2.10)

#### Proof

Under collapse, each c+epsilon is in the uniqueness regime. Hence theta(c+epsilon)^2<=a_n(c+epsilon)<=1, so its logarithm divided by n tends to zero. Apply (2.1) and (2.3) to obtain (2.9).

For (2.10), use the standard fact that critical clusters on nonamenable Cayley graphs are finite almost surely [CF]. In the uniform-edge-label coupling, a finite critical root cluster has only finitely many boundary edges, all with labels strictly above c almost surely. There is therefore a random positive interval immediately above c on which this root cluster does not change. Dominated convergence proves a_n(c+epsilon)->a_n(c) for fixed n. Then use (2.3). QED.

The order of limits in these statements is essential. There is no proved uniformity that exchanges epsilon, n, and R.

The long-time quantity beta(p)=lim_n a_n(p)^(1/n) exists by FKG supermultiplicativity. Its spectral interpretation is part of the existing co-spectral-radius framework [AFH], so this is not proposed as a newly discovered independent threshold theory. The useful addition to this research branch is the finite-volume pivotal representation and the explicit mass -log rho that a collapsed window would have to concentrate. We have not ruled out that concentration universally.

## 3. A sharp positive test: dyadic projection decay on regular trees

Let T_(b+1) be the regular tree of degree b+1, b>=2, with critical percolation parameter p=1/b. For an integer N>=1 define

    Q_N(x,y)
      = E[1{x and y in the same cluster, N<=|C_x|<2N}/|C_x|].

Each Q_N is the expected orthogonal projection that averages functions on clusters in the indicated size shell and is zero on other clusters.

### Theorem 5

There are constants 0<c_b<=C_b<infinity such that, for every integer N>=1,

    c_b N^(-3/2) <= ||Q_N||_(2->2) <= C_b N^(-3/2).           (3.1)

Consequently,

    sum_(k>=0) 2^k ||Q_(2^k)||_(2->2) < infinity.             (3.2)

This proves the earlier proposed dyadic sufficient estimate on every regular tree. It recovers an already-known nonuniqueness class, not a new case of the universal conjecture.

### Exact cluster-size law conditional on an open path

Fix a path of ell edges from x to y, and condition on all its edges being open. The path has ell+1 vertices and

    m_ell=(b-1)ell+b+1

incident edges leaving it. Let F(z) be the probability-generating function of a critical forward branch, including its initial vertex. Then

    F(z)=z B(z)^b,          B(z)=1-p+pF(z),

and the conditional total-size generating function is

    z^(ell+1) B(z)^m_ell.

Lagrange inversion gives, for n>=ell+1,

    P(|C_x|=n | the fixed path is open)
      = [m_ell/(bn-ell+1)]
        binom(bn-ell+1, n-ell-1)
        p^(n-ell-1) (1-p)^((b-1)n+2).                        (3.3)

Equivalently, writing D=bn-ell+1 and s=n-ell-1, this is

    (m_ell/D) P(Bin(D,1/b)=s).

For n<ell+1 the probability is zero.

The maximum binomial point probability is at most a b-dependent constant times D^(-1/2). Since D>=(b-1)n and m_ell<=C_b(ell+1), (3.3) implies the uniform bound

    P(|C_x|=n | path open)
      <= C_b(ell+1)n^(-3/2).                                (3.4)

### Proof of the operator upper bound

The unique x-y path must be open, with probability b^(-ell). Using (3.4),

    Q_N(x,y)
      <= C_b N^(-3/2)(ell+1)b^(-ell).                        (3.5)

Let A_ell be the distance-ell adjacency operator of the regular tree. Its norm is

    ||A_0||=1,
    ||A_ell||=b^(ell/2)[(ell+1)-(ell-1)/b], ell>=1.           (3.6)

For completeness, if A is ordinary adjacency, the distance operators obey A_2=A^2-(b+1)I and A_(ell+1)=A A_ell-b A_(ell-1) for ell>=2. Since the spectrum of A is [-2sqrt(b),2sqrt(b)], these are b^(ell/2)[U_ell(t)-b^(-1)U_(ell-2)(t)] at t=A/(2sqrt(b)). Expanding U_ell(cos theta) as a sum of e^(i(ell-2j)theta), the coefficients of the difference are nonnegative: the two endpoints have coefficient one and the ell-1 interior terms have coefficient 1-1/b. Its absolute value is therefore maximized at theta=0, giving (3.6).

The norm of the radial kernel in (3.5) is bounded by

    sum_(ell>=0) (ell+1)b^(-ell)||A_ell||
      <= C_b sum_(ell>=0)(ell+1)^2 b^(-ell/2) < infinity.

Entrywise domination by a nonnegative bounded kernel bounds the l2 operator norm. This proves the upper bound in (3.1).

### Proof of the lower bound

Set ell=0 in (3.3). Stirling's formula gives

    P(|C_o|=n) ~ [(b+1)/sqrt(2pi b(b-1))] n^(-3/2).

Thus

    Q_N(o,o)=sum_(n=N)^(2N-1) P(|C_o|=n)/n
              asymp_b N^(-3/2).

The norm is at least this diagonal entry. Enlarging constants to cover the finitely many small N proves the lower bound. QED.

### Exact norm formula and the numerical pilot

Let h_(ell,n) denote (3.3), and put

    R_(ell,N)=sum_(n=max(N,ell+1))^(2N-1) h_(ell,n)/n,
    phi_ell=[1+(b-1)ell/(b+1)] b^(-ell/2).

All radial coefficients are nonnegative. Formula (3.6) shows that the finite radial polynomial is maximized at the upper adjacency spectral endpoint. Therefore

    ||Q_N|| = R_(0,N) + [(b+1)/b]
                         sum_(ell=1)^(2N-2) phi_ell R_(ell,N). (3.7)

This is a finite formula, not a simulation. For b=3 (the degree-four tree), its floating-point evaluation gives:

| N | ||Q_N|| | N^(3/2)||Q_N|| |
|---:|---:|---:|
| 4 | 0.1211628213 | 0.9693025704 |
| 16 | 0.0324102730 | 2.074257474 |
| 64 | 0.0054235966 | 2.776881470 |
| 256 | 0.0007406399 | 3.033660989 |

The scaled quantity tends to approximately 3.130897852. More generally, with t=b^(-1/2), A=b+1, B=b-1,

    lim_N N^(3/2)||Q_N||
      = [(2/3)(1-2^(-3/2))/sqrt(2pi b(b-1))]
        [A + (1/b){A^2 t/(1-t)
                    +2AB t/(1-t)^2
                    +B^2 t(1+t)/(1-t)^3}].                  (3.8)

To justify passing the limit through (3.7), apply (3.4) and dominate by the summable sequence C_b(ell+1)^2 b^(-ell/2).

The general dyadic criterion is still OPEN. If it held on all nonamenable Cayley graphs at criticality, then for finitely supported f,

    <f,T_pc f> <= sum_k 2^(k+1)<f,Q_(2^k) f>,

and (3.2) would bound T_pc on l2. The implication from critical l2 boundedness to a nonuniqueness interval is the established result in [H1,H2].

## 4. A single FIID finite-cluster process where the dyadic criterion fails

The preceding proof used genuinely percolation-specific cluster statistics. The following construction shows how much is lost by replacing those statistics with invariance and nonamenability alone.

### Theorem 6

On the fixed nonamenable Cayley graph G=T_4 square Z there is a group-equivariant factor of independent vertex labels such that:

* all clusters are finite almost surely;
* E|C_o|=infinity;
* its size-shell averaging operators satisfy

      sum_(k>=0) 2^k ||Q_(2^k)||_(2->2)=infinity.              (4.1)

This is not Bernoulli bond percolation. Its output edges are dependent, and horizontal edges are all absent.

### Construction

At every vertex v=(g,j), independently sample a nonnegative integer L_v with

    P(L_v>=m)=1/(4m^2), m>=1,
    P(L_v=0)=3/4.

The vertex opens the L_v vertical edges in the interval from (g,j) to (g,j+L_v). Keep the union of all these intervals, and no horizontal edges. This is a measurable equivariant function of independent labels.

### All clusters are finite

For a particular vertical edge, absence means none of the intervals starting to its left covers it. Hence its absence probability is

    q_cut = product_(m>=1) [1-1/(4m^2)] > 0.

The product is positive since the sum of its deficits is finite and each factor is positive. In fact the Wallis product gives q_cut=2/pi, but this value is not needed.

Along each vertical fiber the edge process is stationary and ergodic, being a factor of its independent radius sequence. There are therefore absent edges in both directions with positive density. Each interval component is finite. Countably many fibers give the assertion simultaneously throughout G.

### Infinite susceptibility

For m>=1, a sufficient condition for (e,0) to connect to (e,m) is that an interval starting at (e,-j), for some j>=0, reaches m. The independent radius events imply

    P(o connected to (e,m))
      >= 1-product_(j>=0)[1-1/(4(m+j)^2)]
      >= 1-exp[-(1/4)sum_(k=m)^infinity k^(-2)]
      >= 1-exp[-1/(4m)]
      >= 1/(8m).                                            (4.2)

Summing (4.2) proves E|C_o|=infinity.

### Operator norm calculation

For this process each Q_N is a convolution along Z and acts separately on each fiber. Its entries are nonnegative, and its row sum is

    sum_y Q_N(o,y)=P(N<=|C_o|<2N).                            (4.3)

The l2 norm is at most the row sum by the Schur bound. Conversely, use normalized indicator functions of increasingly long intervals in a single fiber. Because shell clusters have size less than 2N, the kernel has finite range, and the boundary contribution to their Rayleigh quotients vanishes. Thus

    ||Q_N||_(2->2)=P(N<=|C_o|<2N).                            (4.4)

It follows that

    sum_k 2^k ||Q_(2^k)||
      = E[2^(floor(log_2 |C_o|))]
      >= (1/2) E|C_o| = infinity.

This proves (4.1). QED.

The ambient nonamenability is elementary: horizontal boundary in each height slice is bounded below by the tree's positive edge expansion, and summing over slices gives positive expansion of G.

This construction does not refute the universal critical Bernoulli dyadic estimate. It rules out deriving it from nonamenability + finite clusters + FIID admissibility alone. Heavy-tailed intervals retain an amenable direction in which cluster averages have large operator norms. In ordinary Bernoulli percolation, all incident edges have a common independent retention law; a successful proof must use additional structure of that kind or something equally restrictive.

## 5. Resulting research priority

The principal remaining target in the pivotal branch is now to prove B(epsilon)<-log rho for some epsilon>0 on each nonamenable Cayley graph. The stronger B(epsilon)->0 would also suffice. Neither is proved here.

A possible mechanism would control how successive multi-edge bottlenecks can concentrate sensitivity at scales increasing with n. Counting only original bridges is insufficient, as Proposition 1 demonstrates. The bridge-tree viewpoint remains useful, but its evolution under the parameter change is part of the problem, not a negligible correction.

The projection branch now has a sharp benchmark: order N^(-3/2) on regular trees, and an explicit FIID counterexample once the Bernoulli assumption is removed. The next analytical step would need to prevent large size-shell projection mass from aligning along slowly varying, nearly amenable directions. A bound on a single root overlap is not enough: it is a trace moment, not an operator-norm bound. Any proposed argument must control arbitrary test functions or sufficiently high spectral moments.

No new comparison between the costs of arbitrary free actions is proved. The FIID distinction remains substantive: [HP, Remark 4.4] explains why a low-cost invariant percolation construction can cease being FIID before producing the positive-frequency cluster needed to upgrade a minimum-cost result to a maximal/Bernoulli-cost result. The sparse-spine and positive-Farber-rank-gradient branches from the previous note are still OPEN and were not resolved in this continuation.

## 6. Replay and Cairn semantics

`scripts/replay_exploration.py` uses the Python standard library. It independently compares the conditional cluster-size formula to truncated generating-function recursion, verifies radial spectral endpoint recurrences, checks rational strictly subcritical thinning inequalities, checks critical and pivotal inequalities for lazy walks on regular trees, and checks the radius law and finite Wallis products.

The completed replay passed 1,482 exact finite checks:

* 702 cluster-size coefficient identities;
* 120 radial endpoint recurrence identities;
* 300 thinning inequalities;
* 120 lazy-tree-walk checks;
* 200 probability-law telescoping identities;
* 40 finite product identities.

It also evaluates 27 finite radial norm sums in floating point and produces the thinning-bound table. These numerical tables are not Monte Carlo and have no sampling confidence intervals; they are not interval-arithmetic certifications either. The written proofs, not the table, establish the asymptotic exponents and infinite-volume conclusions.

The additive Cairn nodes distinguish established restricted statements, proved conditional implications, published prerequisites, and OPEN universal estimates. Compilation checks dependency consistency, not mathematical validity. Neither universal goal is closed.

## References checked in this continuation

[H1] Tom Hutchcroft, *Percolation on Hyperbolic Graphs*, especially Proposition 6.4 and the critical l2 criterion. https://arxiv.org/html/1804.10191v3

[H2] Tom Hutchcroft, *The L2 boundedness condition in nonamenable percolation*, introduction and operator consequences. https://arxiv.org/html/1904.05804v2

[AFH] Miklos Abert, Mikolaj Fraczyk, and Ben Hayes, *Co-spectral radius for countable equivalence relations*, Ergodic Theory and Dynamical Systems 44 (2024), 3385–3427. Especially the annealed exponent and Section 5.1. https://arxiv.org/html/2205.06692v4

[J] Svante Janson and Lutz Warnke, *On the critical probability in percolation*, Section 2, finite two-point Russo differentiation. https://arxiv.org/html/1611.08549v1

[CF] Itai Benjamini, Russell Lyons, Yuval Peres, and Oded Schramm, *Critical percolation on any nonamenable group has no infinite clusters*, Annals of Probability 27 (1999), 1347–1356; also referenced in [H1].

[HP] Tom Hutchcroft and Gabor Pete, *Kazhdan groups have cost 1*, especially Remark 4.4. https://link.springer.com/article/10.1007/s00222-020-00967-6
