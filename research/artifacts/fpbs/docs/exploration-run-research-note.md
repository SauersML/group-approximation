# Exploration: pivotal geometry, a sharp cactus bound, and critical cluster projections

Date: 2026-09-08 (America/Chicago).

## Status and scope

This continuation tests the proposed pivotal-budget and cluster-projection programs. It establishes the elementary results and conditional reductions proved below. It does not establish the universal pivotal budget, the universal critical L2 bound, the Fixed Price conjecture, or the Benjamini–Schramm conjecture. No claim of mathematical priority is made. The successful classes below are pilot geometries, not newly resolved universal percolation cases.

Main outcomes:

* Conditional expected pivotal counts do **not** form a metric, even on a nonamenable Cayley graph at its critical parameter.
* Nevertheless, on every locally finite cactus graph, conditional expected pivotal counts are at most `(1+exp(-2))` times ambient distance. The constant is optimal across this class. The estimate also gives the finite-ball, random-walk pivotal budget required by the preceding note.
* There are degree-three finite networks with adjacent terminals and an unbounded expected pivotal count at a fixed parameter. Thus neither adjacency nor bounded degree controls the count. A nonamenable, nontransitive augmentation preserves this obstruction.
* On a regular tree, the proposed dyadic cluster-averaging operators satisfy `||Q_k|| <= C 2^(-3k/2)`. The proof retains geometry, rather than using the cluster-size tail alone.
* The integrated pivotal sensitivity has an exact expression in terms of an exponential random-walk connectivity rate. A collapsed nonuniqueness interval would force a right-hand jump of that rate at criticality.

All computational claims refer to `scripts/replay_exploration.py` and its saved output. Exact checks, numerical evaluations, and infinite proofs are distinguished below.

## 1. Definitions and finite-volume identity

For independent bond percolation with retention probability `p`, let

    tau_p(x,y) = P_p(x connected to y).

For a finite graph, let `N_p(x,y)` be the number of open edges whose removal destroys the connection, on the event that the connection exists. Set

    D_p(x,y) = E_p[N_p(x,y) | x connected to y].

The notation `D` is not an assertion that this is a metric.

Finite-volume differentiation gives

    D_p(x,y) = p (d/dp) log tau_p(x,y).                 (1.1)

This is the finite Russo identity: pivotality does not depend on the state of the tested edge, and an open pivotal edge forces an increasing event. The same identity holds when the endpoint is an independent random-walk endpoint, after averaging over that endpoint. For the infinite arguments we always first apply the identity in a finite induced ball; there is no interchange of infinite differentiation and expectation.

The previous note proposed a graph-dependent constant `C` and a parameter `p0>pc` such that, for all `n>=1`, all radii `R>=n`, and all `p in [pc,p0]`,

    E_p[N_{n,R} | o connected to X_n inside B_R] <= C n. (PB)

Its conditional implication to nonuniqueness uses Schramm's estimate [H18, Proposition 6.4]. The universal assertion (PB) remains open here.

## 2. An exact obstruction to a metric charging argument

### 2.1 Six-cycle calculation

On the cycle `C_m`, vertices at cyclic separation `r`, where `1<=r<=m-1`, have two edge-disjoint possible simple routes, of lengths `r` and `m-r`. Therefore

    tau_r(p) = p^r + p^(m-r) - p^m,

and

    D_r(p) = [r p^r + (m-r)p^(m-r) - m p^m]
             / [p^r + p^(m-r) - p^m].                 (2.1)

On `C_6` at `p=1/2`,

    D_1 = 12/11,
    D_2 = 42/19,
    D_2 - 2D_1 = 6/209 > 0.                           (2.2)

Thus `D(0,2)>D(0,1)+D(1,2)`. The pointwise bridge-tree distance in a fixed connected configuration is a metric, but conditional expectations taken under different connection events need not preserve the triangle inequality.

### 2.2 The same failure on an infinite nonamenable Cayley graph

Take

    Gamma = C_6 * C_2 = <a,b | a^6=b^2=1>,
    S = {a,a^(-1),b}.

Its Cayley graph consists of disjoint hexagons, joined by the `b`-edges in a tree pattern. Contracting the hexagons gives a degree-six tree. In particular, the graph is nonamenable: for a finite vertex set A, let f be the number of entirely occupied hexagons and t the number of partially occupied hexagons. The union B of its f+t occupied hexagons has at least `4(f+t)` outgoing b-edges, and at most `6t` of these can originate at missing vertices in the partial hexagons. If `t<=f`, at least `4f-2t>=2f` b-boundary edges of A remain. If `t>f`, the cycle boundary contributes at least `2t`. Since `|A|<=6(f+t)`, both cases give `|boundary A|>=|A|/6`.

Every simple path whose endpoints lie in one hexagon stays in that hexagon: leaving and returning through the quotient tree would force a repeated vertex. Consequently, (2.1) remains exactly valid in this infinite graph.

The failure also occurs at its critical parameter, not just at `p=1/2`. When a percolation exploration enters a new hexagon across a b-edge, its forward offspring mean is

    M(p) = p sum_{j=1}^5 tau_j(p)
         = 2p^2+2p^3+2p^4+2p^5+2p^6-5p^7.           (2.3)

The forward explorations use disjoint hexagons and distinct forward b-edges, giving an ordinary finite-offspring branching process. The root has a different initial offspring distribution, which does not change the threshold. Hence `pc` is the unique root of `M(p)=1` in `(0,1)`.

Exact arithmetic gives

    M(513/1000)<1<M(514/1000),

so

    0.513 < pc < 0.514.

For the triangle defect,

    D_2(p)-2D_1(p)
       = -2p^2(p-1) F(p)
         / [(p^2-p+1)(p^3-p-1)(p^4-p^2-1)],

    F(p)=3p^6+p^5-3p^4-5p^2+p+1.

The denominator is positive for `0<p<1`. On `[0.513,0.514]`, a rational lower bound obtained by bounding each positive and negative monomial separately is

    F(p) >= 3(0.513)^6+(0.513)^5
            -3(0.514)^4-5(0.514)^2+0.513+1
          > 0.0728.

Thus the defect is positive at `pc`, and by continuity on a neighborhood of it. This refutes the metric shortcut in the actual nonamenable Cayley setting. It does **not** refute (PB).

## 3. A replacement theorem: the optimal cactus bound

A cactus graph here is a connected locally finite graph whose blocks are single edges or finite cycles. Equivalently, distinct simple cycles share at most one vertex. Cycle lengths need not have a common upper bound.

### Theorem 3.1

For independent bond percolation on a cactus graph and any connected pair of vertices x,y,

    E_p[N_p(x,y) | x connected to y]
        <= (1+exp(-2)) d_G(x,y),   0<p<1.             (3.1)

The constant `1+exp(-2)` is optimal uniformly over cactus graphs and parameters.

If `x=o`, `d_G(o,y)<=R`, and connections are restricted to the induced ambient ball `B_R(o)`, the same estimate holds with the original ambient distance on the right.

### 3.1 The sharp cycle inequality

For a cycle with route lengths `r<=ell`, put

    a=p^r in (0,1),   t=ell/r>=1.

Using the disjoint route possibilities, (2.1) becomes

    D_p(x,y)/r
      = [a(1-a^t)+t a^t(1-a)] / [a+a^t-a^(t+1)].

Subtracting one gives

    D/r - 1 = a^(t-1)[t(1-a)-1]
              / [1+(1-a)a^(t-1)].                    (3.2)

Set

    z=-log a>0,
    v=(1-a)/z,
    u=(t-1)z>=0.

The numerator of (3.2) is `exp(-u)(v u-a)`. Its maximum over `u>=0` is

    v exp(-1-a/v).

If this numerator is negative the desired upper bound is automatic; otherwise the denominator in (3.2) is at least one. It therefore suffices to prove

    v exp(-1-a/v) <= exp(-2),

or equivalently

    a/v - log v - 1 >= 0.                            (3.3)

With `a=exp(-z)`, the left side of (3.3) is

    H(z)= z/(exp(z)-1) - log((1-exp(-z))/z) - 1.

It has limit zero at `z=0`, and

    H'(z) = 1/z - z exp(z)/(exp(z)-1)^2 >= 0,

because `2 sinh(z/2)>=z`. This proves (3.3), hence (3.1) for a cycle.

For sharpness, take `r=1`, `ell=t` an integer tending to infinity, and `p=1-2/t`. Then `a->1`, `a^(t-1)->exp(-2)`, and `t(1-a)-1=1`. Formula (3.2) tends to `exp(-2)`. Thus no smaller universal constant works.

### 3.2 Assembling cycles and bridges

Between fixed endpoints of a cactus there is a unique chain of blocks. A simple connecting path must cross this chain; excursions into other blocks cannot connect different vertices of a chain block.

The required block-connection events depend on disjoint edge sets. Their probabilities multiply, so their logarithmic derivatives add. Bridge blocks contribute one pivotal edge. Cycle blocks contribute at most `(1+exp(-2))` times the shorter arc length, by the preceding calculation.

The sum of these bridge lengths and shorter arc lengths is exactly the ambient distance between the endpoints. This proves (3.1).

For a ball rooted at o, the chain to y contains an ambient geodesic, entirely inside the ball. Each chain cycle is either fully present, or offers only its geodesic route from the entry point to the exit point. In the latter case its pivotal count is exactly that route length. In particular, the ball restriction cannot remove the shortest route and leave only a longer one. The same bound follows.

### 3.3 Consequence for the random-walk budget

For `R>=n`, every possible n-step random-walk endpoint satisfies `d_G(o,X_n)<=n`. Condition first on the endpoint and its connection event and apply the finite-ball version of (3.1). Averaging with the conditional endpoint distribution gives

    E_p[N_{n,R} | o connects to X_n inside B_R]
        <= (1+exp(-2)) n.                             (3.4)

Thus (PB) is proved on cactus graphs, with one constant independent of p, cycle lengths, n, and R. This improves the earlier crude bound depending on the largest number of edges in a block. It is a check of the proposed method in a tractable class, not a claim that the nonuniqueness conjecture was previously unresolved in that class.

For a nonamenable Cayley cactus, Schramm's bound and finite-volume Russo integration give nonuniqueness for

    pc < p < min{1, pc rho^(-1/(1+exp(-2)))}.

This is a sufficient interval, not necessarily the full nonuniqueness interval.

## 4. A bounded-degree obstruction to a purely local argument

The next example does not contradict the cactus theorem: its cycles overlap in a genuinely multiscale way.

### 4.1 Recursive network

Let H_0 be a single edge with terminals s,t. To form H_{k+1}, make two parallel branches, each consisting of two independent copies of H_k in series. Attach a fresh terminal edge at each end of this parallel structure. Terminals of H_k have degree one, and all vertices have degree at most three.

Let `r_k(p)` be the terminal connection probability. Independence gives

    r_0(p)=p,
    r_{k+1}(p)=p^2(2r_k(p)^2-r_k(p)^4).               (4.1)

For k>=1 add one direct edge between the two terminals, forming J_k. This remains a simple graph of maximum degree three, and its terminals are adjacent. Their connection probability is

    t_k(p)=p+(1-p)r_k(p).                             (4.2)

The number of edges of J_k is `(5*4^k+1)/3`.

### 4.2 Exact critical recursion calculation

Define

    q*=sqrt(2/3),
    p*=sqrt(3/(4q*)) = 0.9584146563...,
    f(x)=(p*)^2(2x^2-x^4).

Then

    f(q*)=q*,   f'(q*)=1,
    f''(q*)=-3sqrt(6)/2.

For `r_0=p*>q*`, the sequence `r_{k+1}=f(r_k)` decreases to q*. Indeed, `x(2-x^2)` has its maximum at q*, so `f(x)<x` for `q*<x<=1`, while f is increasing on `[q*,1]` and maps it into `[q*,1]`.

Put `A=3sqrt(6)/4` and `epsilon_k=r_k-q*`. Taylor expansion gives

    epsilon_{k+1}=epsilon_k-A epsilon_k^2+O(epsilon_k^3).

Thus `1/epsilon_{k+1}-1/epsilon_k -> A`, and

    epsilon_k ~ 1/(A k).

For `v_k=r'_k(p*)`, differentiation of (4.1) gives

    v_{k+1}=f'(r_k)v_k + 2p*(2r_k^2-r_k^4).

Here

    f'(r_k)=1-2/k+o(1/k),
    2p*(2r_k^2-r_k^4)->2q*/p*.

The coefficients f'(r_k) lie in `[0,1]`, so `v_k=O(k)`. Dividing the recurrence by k, or bounding its coefficient and forcing term above and below by arbitrarily close `1-(2+/-eta)/k` and `2q*/p*+/-eta`, yields

    v_k/k -> 2q*/(3p*).                              (4.3)

Applying (1.1) to (4.2),

    E_{p*}[N(s,t) | s connected to t in J_k]
       = p*[(1-r_k)+(1-p*)v_k]/[p*+(1-p*)r_k]
       ~ c* k,

where

    c* = 2(1-p*)q* / [3(p*+(1-p*)q*)]
       = 0.022810260226... > 0.                       (4.4)

Thus the conditional pivotal count becomes arbitrarily large although the terminals remain adjacent and the maximum degree stays three. Their connection probability converges to the positive constant `p*+(1-p*)q*`, approximately 0.99237, so rare conditioning is not the sole explanation.

The numerical samples in the replay evaluate this exact recursion, not explicit graphs with exponentially many edges. For example, the mean counts at depths 100, 1000, and 10000 are approximately 2.65986, 23.28941, and 228.68094.

### 4.3 Adding nonamenability does not fix the local statement

Attach a separate infinite rooted binary tree by one edge to every vertex of J_k. The resulting graph has maximum degree four and is nonamenable, uniformly in k. To see this directly, orient each attached tree away from its core vertex. Each core vertex has one outgoing tree edge; each non-core vertex has two. For a finite set A with c core vertices and t tree vertices, at most t of the `c+2t` outgoing edges are internal. At least `c+t=|A|` therefore cross its boundary.

A simple path between two core vertices cannot use an attached tree and return. Consequently the core connection probability and pivotal count are unchanged. These are nontransitive graphs, with critical parameter 1/2, whereas the obstruction was evaluated at p*. No claim about the near-critical pivotal budget for Cayley graphs follows from them.

The exact conclusion is narrower: bounded degree, short endpoint distance, high connection probability, and even a uniform ambient expansion bound do not alone give a uniform pivotal estimate at arbitrary p. A proof of (PB) must use its near-critical and homogeneous structure, or some other additional ingredient.

## 5. A successful operator pilot on regular trees

Let `T_{q+1}` be the regular tree of degree q+1, where `q>=2`, and let `pc=1/q`. At pc all clusters are finite; this follows directly from the critical finite-variance branching process with offspring distribution `Binomial(q,1/q)`.

For a dyadic shell `N=2^k`, define the averaged cluster projection

    Q_k(x,y)=E_pc[1{x connected to y, N<=|C_x|<2N}/|C_x|].

### Theorem 5.1

There is a constant C_q such that

    ||Q_k||_{2->2} <= C_q 2^(-3k/2).                  (5.1)

In particular, `sum_k 2^k ||Q_k||<infinity` on regular trees. This verifies the previously proposed dyadic criterion in this model; the universal dyadic estimate remains open.

### 5.1 Branch generating function

Let F(z) generate the number of vertices contributed through a particular incident edge, including zero when that edge is closed. At criticality,

    F(z)=(q-1)/q + z F(z)^q/q.                        (5.2)

For vertices x,y at distance r, the unique path has r+1 vertices. Conditional on its r edges being open, it has

    m_r=(q-1)r+q+1

off-path branches. Consequently,

    E_pc[z^|C_x| 1{x connected to y}]
       =q^(-r) z^(r+1) F(z)^m_r.                     (5.3)

Formal Lagrange inversion applied to (5.2) gives, for m>=1,

    [z^n]F(z)^m
      = (m/(qn+m)) binom(qn+m,n)
        q^(-n) ((q-1)/q)^((q-1)n+m).                 (5.4)

For n=0 this formula reads `((q-1)/q)^m`. The replay verifies (5.4) against direct fixed-point power-series expansion, without using (5.4) to generate that expansion.

The binomial probability in (5.4) is at most `C_q(qn+m)^(-1/2)` by the elementary maximal binomial mass bound (or Stirling's inequalities). Hence

    [z^n]F(z)^m <= C_q m/(n+1)^(3/2).                 (5.5)

This bound is uniform in m,n, with q fixed.

### 5.2 Retaining the tree geometry

Let `H_N(x,y)=P_pc(x connected to y, |C_x|=N)` and write its radial value as `h_N(r)`. From (5.3),

    h_N(r)=q^(-r)[z^(N-r-1)]F(z)^m_r,   0<=r<N.

For `r<=N/2`, (5.5) gives

    h_N(r)<=C_q q^(-r)(r+1)N^(-3/2).                 (5.6)

For `N/2<r<N`, simply use `h_N(r)<=q^(-r)`.

Let S_r be the operator summing a function over the sphere of radius r. Its norm satisfies

    ||S_r|| <= C (r+1)q^(r/2).                        (5.7)

For completeness, `S_1=A`, `S_2=A^2-(q+1)I`, and `S_{r+1}=AS_r-qS_{r-1}` for r>=2. The adjacency spectrum is `[-2sqrt(q),2sqrt(q)]`; the upper bound follows from the weighted Schur test with weight `q^(-distance/2)`, and the endpoints follow by truncated radial test functions (with the negative endpoint obtained by bipartite sign change). The recurrence and the bound `|U_r(t)|<=r+1` for Chebyshev polynomials on `[-1,1]` imply (5.7).

Combining (5.6), (5.7), and the crude bound for r>N/2,

    ||H_N||
      <= C_q N^(-3/2) sum_{r<=N/2}(r+1)^2 q^(-r/2)
         + C_q sum_{r>N/2}(r+1)q^(-r/2)
      <= C'_q N^(-3/2).                              (5.8)

The exponentially small second sum is absorbed into the last bound, uniformly in N.

Finally,

    Q_k = sum_{j=N}^{2N-1} H_j/j,

so

    ||Q_k|| <= C'_q sum_{j=N}^{2N-1} j^(-5/2)
             <= C''_q N^(-3/2).

This proves (5.1).

### 5.3 Exact radial norm formula used for numerical evaluations

For a finite radial nonnegative kernel `H=sum_r c_r S_r`, `c_r>=0`, the maximum of each sphere polynomial in absolute value occurs at the positive adjacency spectral endpoint. Indeed,

    S_r = q^(r/2)[U_r(A/(2sqrt(q)))-q^(-1)U_{r-2}(A/(2sqrt(q)))],

and its expansion in cosine functions has nonnegative coefficients. Thus for r>=1,

    ||S_r||=q^(r/2)[r+1-(r-1)/q],

and all the maximizing endpoints align. Hence

    ||H_N|| = h_N(0)
       + sum_{r=1}^{N-1} h_N(r)q^(r/2)[r+1-(r-1)/q].  (5.9)

The same alignment holds for the sums defining Q_k. The replay evaluates these exact finite coefficient expressions numerically for the degree-three tree, at dyadic sizes through 128. These computations illustrate the proven bound; they do not prove the asymptotics or a universal result.

The useful mechanism is the summable factor `q^(-r/2)`: the loss from the spherical operator norm is outweighed by the cost of forcing the unique open path. On a general Cayley graph, overlapping alternate routes prevent inserting the same path factor without further proof.

## 6. The refined target: integrated sensitivity and an exponential rate

Let G be a nonamenable Cayley graph, X simple random walk, and `rho=||P||<1`. Define

    a_n(p)=P_p(o connected to X_n),
    lambda(p)=lim_{n->infinity} a_n(p)^(1/n), p>0.     (6.1)

### 6.1 Existence and critical value

Positive association and translation invariance give

    tau_p(o,xy)>=tau_p(o,x)tau_p(o,y).

Averaging over independent n-step and m-step increments gives

    a_{n+m}(p)>=a_n(p)a_m(p).

Moreover, `a_n(p)>=p^n>0`, by opening the edges of the walk itself. Fekete's lemma therefore gives existence of (6.1), with

    lambda(p)=sup_n a_n(p)^(1/n).

Since `a_{2n}(p)>=P(X_{2n}=o)`, the return-probability spectral-radius identity yields `lambda(p)>=rho`. The latter identity follows from the spectral theorem for the regular random-walk operator; the canonical root trace is faithful on invariant operators, so its even moments detect the full spectral radius.

Schramm's lemma gives `a_n(pc)<=rho^n` [H18, Proposition 6.4], and hence

    lambda(pc)=rho.                                  (6.2)

The same cited proposition actually gives `lambda(p)=rho` throughout `0<p<=p_{2->2}`. We need only (6.2).

### 6.2 Exact integrated pivotal identity

Write `E_{n,R}={o connects to X_n inside B_R}` and `a_{n,R}(p)=P_p(E_{n,R})`. Finite Russo integration gives

    (1/n) int_pc^p E_s[N_{n,R}|E_{n,R}] ds/s
       = (1/n) log(a_{n,R}(p)/a_{n,R}(pc)).            (6.3)

For each n, both finite-ball probabilities increase to the corresponding infinite-volume probabilities and remain positive. Thus the limit in R of the integral exists, even though no monotonicity of its integrand is claimed.

Taking R->infinity first and then n->infinity in (6.3),

    lim_n lim_R (1/n) int_pc^p E_s[N_{n,R}|E_{n,R}] ds/s
       = log(lambda(p)/rho).                         (6.4)

In particular, this integrated sensitivity per walk step lies in `[0,-log rho]`.

### 6.3 What a collapsed window would force

If percolation at p>pc has a unique infinite cluster, positive association gives

    tau_p(x,y)>=theta(p)^2>0

for every pair. Thus `a_n(p)>=theta(p)^2` and

    lambda(p)=1.                                     (6.5)

Consequently, a hypothetical equality `pc=pu` would force

    lambda(pc)=rho<1,
    lambda(p)=1 for every p>pc.                       (6.6)

Equivalently, the left side of (6.4) would equal the fixed positive amount `-log rho` on every interval `(pc,pc+epsilon)`, however narrow.

A sufficient refined target is therefore

    lim_{epsilon downarrow 0}
      lim_n lim_R (1/n) int_pc^(pc+epsilon)
          E_s[N_{n,R}|E_{n,R}] ds/s = 0.              (IS)

It would be enough to show that the limit/supremum here is strictly below `-log rho`; zero is a clean stronger target. The pointwise budget (PB) implies (IS), since its integral is at most `C log((pc+epsilon)/pc)`. But (IS) allows narrow spikes and does not ask for a uniform linear bound at every parameter and every radius.

This is a proved conditional reduction, not a proof of (IS). Continuity of each fixed-n connection probability does not imply continuity of the exponential rate: n->infinity is a load-bearing limit. The hierarchical example explains why pointwise sensitivity control is a substantial additional demand, while the cactus theorem supplies a successful structural test.

## 7. Research disposition

Established within this note: the Cayley-graph metric counterexample; the sharp cactus estimate and its finite-ball budget consequence; the bounded-degree hierarchical obstruction; the regular-tree dyadic estimate; and the integrated-rate identities and conditional implication.

Still open in this work: the universal (PB) estimate, the universal dyadic estimate, the integrated regularity target (IS), both universal original conjectures, and the earlier Fixed Price sparse-spine/rank-gradient branches. This continuation focuses on percolation and makes no additional claim about equality of action costs.

The most concrete next proof target is a structural bound on repeated pivotal amplification for homogeneous, overlapping-cycle graphs. A successful argument must not assume the metric inequality refuted in Section 2, and must distinguish the nested obstruction of Section 4 from the additive block structure of Section 3. The integrated formulation in Section 6 permits considerably more flexibility than a uniform pointwise bound.

## 8. Verification limits

The replay performs:

* 2,040 exhaustive cycle configurations, verifying 132 pairs of probability/pivotal identities at rational parameters;
* an exact six-cycle defect and exact critical-parameter bracket/sign certificate;
* a rational-parameter sweep of the cycle bound and numerical sharpness limits;
* a symbolic derivative identity supporting the analytic sharp bound;
* five finite recursive-network structure checks and 128 exhaustive depth-one configurations;
* high-precision evaluation of the exact hierarchical recurrence, not enumeration of enormous graphs;
* 408 exact critical branch-coefficient checks against independently expanded generating functions;
* finite radial coefficient evaluations for illustrative tree operator norms.

These are not Lean proofs. Cairn checks research-node dependencies and artifact availability, not mathematical validity. Universal nodes remain open.

## References consulted

[H18] Tom Hutchcroft, *Percolation on Hyperbolic Graphs*, arXiv:1804.10191v3, especially Proposition 6.4 (Schramm's estimate), the phase definitions, and Section 2. https://arxiv.org/html/1804.10191v3

[H19] Tom Hutchcroft, *The L2 boundedness condition in nonamenable percolation*, arXiv:1904.05804v2. The critical L2 route is a sufficient criterion; it is not an automatic consequence of nonamenability in this note. https://arxiv.org/html/1904.05804v2

[K] Gady Kozma, *Percolation on a product of two trees*, arXiv:1003.5240v3. Background on Schramm's lemma and on geometry-sensitive critical estimates. https://arxiv.org/html/1003.5240v3

[HT] Tom Hutchcroft and Matthew Tointon, *Non-triviality of the phase transition for percolation on finite transitive graphs*, arXiv:2104.05607. Consulted as a check on the role of homogeneity and on uniform critical-probability gaps; no theorem from it is needed for the elementary counterexamples or sharp cactus proof. https://arxiv.org/abs/2104.05607
