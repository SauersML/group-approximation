# Fractional-cut repair and explicit low-cost, nowhere-hyperfinite seeds

Research continuation — September 9, 2026

## Status and attribution

This note derives a measurable repair theorem from fractional product-space Hölder inequalities and weighted cut counting. It proves an explicit separation from the previous whole-path second-moment certificate. It also constructs, inside the original Bernoulli orbit relation of every countable nonamenable group, nested ergodic treeable subrelations of every cost in [1,2], with every positive-measure restriction nonhyperfinite at costs above one.

The seed construction is a consequence of published Gaboriau–Lyons and Miller–Tserunyan theorems and standard cost results; it is not represented as a newly discovered existence theorem. The finite network inequalities are applications of established probabilistic tools, with complete proofs of the versions needed here. No priority or independent-verification claim is made for the combined measurable statements. Neither universal Fixed Price nor universal Benjamini–Schramm is proved. In particular, the seed construction and the network-repair criterion have NOT been fitted together for large odd-exponent Burnside groups.

No previous broad bounded-exponent or two-generator theorem is a premise of this note. Earlier Cairn records are preserved as provenance, not independently revalidated.

## 1. Action and certificate conventions

Let a countable group Gamma act essentially freely and probability-preservingly on a standard probability space (X,mu), with right notation x -> xg. Work modulo a common invariant null set. Write R for its orbit relation and S <= R for a fixed countable measurable subequivalence relation.

For S <= T let

    relC(T;S) = inf { C(Psi) : S joined with R_Psi equals T }.

Graphing cost is the sum of the measures of the domains of its partial p.m.p. bijections. Added maps below are restrictions of the transformation T_a:x->xa. Cost counts these maps once, not the lengths of paths already in S. All infimum statements allow arbitrarily small approximation errors. These are standard cost conventions [G,L].

Fix a in Gamma. At a root x not already S-connected to xa, a finite *network certificate* consists of:

* a finite undirected multigraph H_x, with between 2 and v vertices;
* a representative z_u(x) in the orbit of x for every abstract vertex u, with distinguished vertices representing x and xa (equivalently their S-classes);
* for every edge e={u,w}, a specified finite path from z_u to z_w, using only S-connections and unoriented a-edges {y,ya};
* the finite support P_e(x) of starting points y whose a-edges must be selected to make that edge-path available;
* nonnegative weights w_e(x).

A reversed traversal uses the starting point of its underlying forward T_a edge. Repeated occurrences of the same starting point in one support are counted once. Loops may be discarded. Edges with empty support connect S-equivalent representatives and may be contracted in advance. We require nonempty supports for positive-weight edges.

All objects are measurable and fixed BEFORE the auxiliary coloring used in the proof. The paths, supports and weights may depend on x and on S. Their total lengths and orbit displacement need not be uniformly bounded. For the uniform theorem below only the NUMBER of selected a-edges per edge-path is bounded.

The load constraints are

    sum_{e : y in P_e(x)} w_e(x) <= 1                  (1.1)

for each distinct tested point y. The weighted GLOBAL minimum cut is

    kappa_x = min_{empty != A proper subset V(H_x)}
                  sum_{e crossing A} w_e(x).          (1.2)

This is not merely an s-t minimum cut. Vertices and edges are abstract bookkeeping for real valid paths in the target action, not extra probability-space sheets.

## 2. The finite fractional product inequality

### Lemma 2.1

Let independent variables (xi_y) be given on a finite product probability space. Suppose nonnegative functions f_e depend only on the coordinate set P_e. If w_e>=0 and the load constraints (1.1) hold, then

    E product_e f_e^(w_e) <= product_e (E f_e)^(w_e).    (2.1)

Zero weights are omitted. The needed version is finite and bounded. This is the fractional form of the product-space Hölder/Shearer mechanism; see [F,GLSS] for the established theory.

**Proof.** Integrate one coordinate y at a time. Conditional on the other coordinates, apply Hölder to the factors f_e^(w_e) involving y with exponents 1/w_e, adding the constant function 1 with the leftover reciprocal exponent if their sum is below one. This replaces each affected f_e by its expectation in y, retaining the outer exponent w_e. Repeat over the remaining coordinates. Fubini yields (2.1). QED.

Select each tested point independently with probability q in (0,1). An edge e of the certificate network is declared open when all points of P_e are selected. Assume |P_e|<=L. For any cut A, let f_e be the indicator that edge e is closed. Because an indicator satisfies f_e^w_e=f_e for w_e>0, (2.1) gives

    P(all positive-weight crossing edges are closed)
       <= product_{e crossing A}(1-q^|P_e|)^(w_e)
       <= exp( -q^L sum_{e crossing A} w_e ).          (2.2)

This allows arbitrary shared selected points. The edge-open events need not be independent. The fractional load constraints pay for their dependencies.

## 3. Weighted cut counting, with the needed proof

### Lemma 3.1

A finite weighted undirected multigraph with v>=2 vertices and global minimum cut kappa>0 has at most v^(2j) cuts of weight at most j*kappa, for each integer j>=1. Cuts are unordered nontrivial bipartitions.

This is the integer-parameter version of the Karger–Stein cut-counting theorem [K].

**Proof.** If v>2j, contract random edges, selected proportionally to their weights, until 2j supervertices remain. A fixed cut of weight at most j*kappa survives a contraction at r>2j supervertices with conditional probability at least 1-2j/r: every current cut has weight at least kappa, so total edge weight is at least r*kappa/2. Hence its survival probability is at least

    product_{r=2j+1}^v (1-2j/r) = 1/binom(v,2j).

Choose a uniformly random nontrivial bipartition of the remaining supervertices. Each surviving original cut is then output with probability at least 1/(2^(2j-1)-1). Distinct outputs are disjoint events, so the number of the designated cuts is at most

    binom(v,2j)(2^(2j-1)-1) <= v^(2j).

The inequality uses 2^(2j-1)<= (2j)!. If v<=2j, the total number 2^(v-1)-1 of cuts is already at most v^(2j). Real nonnegative weights cause no difficulty: contraction is directly weight-proportional and zero-weight edges are ignored. QED.

### Lemma 3.2: correlated-network reliability

Under the assumptions of Section 2, let H have at most v vertices and global weighted minimum cut at least kappa. If v^2 exp(-kappa q^L)<1, then

    P(the open certificate network is disconnected)
       <= v^4 exp(-kappa q^L)
                   / (1-v^2 exp(-kappa q^L)).         (3.1)

**Proof.** Failure of connectivity leaves a cut with all crossing edges closed. Group cuts by weights in [j*kappa,(j+1)*kappa), j>=1. Lemmas 2.1 and 3.1 bound the union probability by

    sum_{j>=1} v^(2(j+1)) exp(-j*kappa q^L),

which is the series in (3.1). The use of the global minimum cut is essential. QED.

In particular, for 0<epsilon<1,

    kappa q^L >= 4 log v + log(2/epsilon)              (3.2)

implies that (3.1) is at most epsilon: the numerator is at most epsilon/2, while the denominator is at least 1-epsilon/(2v^2)>=7/8.

## 4. The measurable fractional-cut repair theorem

### Theorem 4.1

Let S <= R and a in Gamma be fixed. Suppose outside a set of roots of measure at most delta we have network certificates as in Section 1, satisfying

    |V(H_x)| <= v,       1 <= |P_e(x)| <= L,
    load at each tested point <=1,
    global minimum cut >=kappa>0.

Roots already S-connected to xa need no certificate and count as automatic successes. If (3.2) holds for q,epsilon in (0,1), then

    relC(S joined with R_<a>;S) <= q+delta+epsilon.      (4.1)

All networks and S belong to the originally specified action.

**Proof.** Choose refining finite measurable partitions separating points of a standard Borel model of X. For almost every good root x, the finitely many DISTINCT tested points in its network eventually occupy distinct atoms. Consequently, by dominated convergence there is a finite partition whose collision-exception roots have measure less than any prescribed eta>0. This works for root-dependent networks and an unbounded, but finite at each root, number of tested points.

Select each atom independently with probability q, and let U be their union. At every good root outside the collision exception, the tested labels have the independent law used in Lemma 3.2. Declare D(U) to contain every bad root not already connected in S, and every good root whose selected certificate network does not connect the distinguished vertices. Then

    E_colors mu(U)=q,
    E_colors mu(D(U)) <= delta+epsilon+eta.

The networks, their validity, and their weights do not depend on these colors. Averaging supplies a deterministic measurable U with

    mu(U)+mu(D(U)) <= q+delta+epsilon+eta.

Add T_a restricted to U and to D(U), or just to their union. At a nonfailure root a selected network path expands to a finite path using S and selected a-edges. At a failure root the direct a-edge repairs the connection. Every added edge is an a-edge, so the joined relation is exactly S joined with R_<a>. Let eta decrease to zero in the cost infimum. QED.

### An explicit bound

Provided the bracket is below one, set

    q = [(4 log v + log(2/epsilon))/kappa]^(1/L).

Then

    relC <= [(4 log v + log(2/epsilon))/kappa]^(1/L)
                  +delta+epsilon.                    (4.2)

The trivial direct-edge upper bound can always be used if the displayed quantity is too large. The number L counts NEW selected a-edges per local connector path, not full path lengths inside S, and not the number of local connector paths in an end-to-end route.

For bounded L, a sequence with delta->0 and

    kappa / (log v + log kappa) -> infinity            (4.3)

gives zero relative cost: choose epsilon=1/kappa eventually and use (4.2). For growing L, the exact required condition is

    (1/L) log[kappa/(4 log v + log(2/epsilon))] -> infinity,

with delta,epsilon tending to zero. Merely kappa->infinity is not enough.

## 5. Fractional capacities have a finite optimization certificate

For a fixed network and supports, maximize kappa over edge weights subject to (1.1) and the cut inequalities (1.2). This is a finite linear program. Its dual is

    minimize sum_y z_y
    subject to z_y>=0, alpha_A>=0, sum_A alpha_A=1,
       sum_{y in P_e} z_y >= sum_{A:e crosses A} alpha_A
       for every edge e.                             (5.1)

Here alpha is a probability distribution over nontrivial cuts. One obtains this dual by assigning multipliers to the load and cut constraints; standard finite-dimensional linear-programming duality applies. A positive optimum has matching primal and dual values. The nonempty-support requirement bounds each positive edge weight and makes the primal finite.

Thus a large-looking network cannot hide a single shared necessary edge. If one cut has every crossing edge-path requiring the same starting point y0, its capacity is at most

    sum_{e crossing cut}w_e <= sum_{e:y0 in P_e}w_e <=1.

Equivalently, take alpha concentrated on that cut and z_y0=1 in the dual.

The theorem does not assert an efficient general procedure for finding the path certificates in an infinite action. The LP optimizes a finite certificate AFTER its real paths are supplied. The accompanying finite LP computations are benchmarks, not constructions inside a Burnside action.

## 6. A strict improvement over the preceding whole-path bound

Consider a corridor with m interfaces in series, each containing w parallel alternatives with distinct selection labels. Labels at different interfaces are also distinct. A complete path picks one alternative at each interface.

Under independent q-selection, the exact success probability is

    [1-(1-q)^w]^m.

The paid-repair bound for such a measurable corridor certificate is therefore

    q + 1-[1-(1-q)^w]^m <= q+m exp(-qw).               (6.1)

No independence of different roots is required; the finite-partition proof makes the same rootwise bound usable in the original action. Equivalently, the network has v=m+1, L=1, unit edge weights, and kappa=w, so Theorem 4.1 applies.

Take, for integers j>2,

    m=2^j,        w=j^2,       q=2/j.

Then

    q+failure <= 2/j + exp(-(2-log 2)j) -> 0.           (6.2)

End-to-end paths require 2^j selected edges. A bound requiring uniformly short complete routes would miss this regime. The general conservative constant in Theorem 4.1 also gives vanishing repair for this family: take q=4/j and epsilon=exp(-j) for all sufficiently large j. The exact corridor count permits the sharper q=2/j used in (6.2).

Now apply the PREVIOUS whole-path overlap method to all w^m full paths. Its kernel is

    K(P,Q)=q^(-number of matching choices).

The kernel is positive semidefinite. Independently permuting the w alternatives at every interface is a transitive symmetry preserving it. Averaging any probability weight vector over these symmetries and using convexity of the quadratic form shows that the uniform vector minimizes the overlap energy. Its minimum is exactly

    M_min = [1+(q^(-1)-1)/w]^m.                        (6.3)

Thus the best previous second-moment failure bound is 1-1/M_min. With m=2^j, w=j^2, q=2/j, M_min->infinity, so that failure bound tends to ONE, whereas the actual failure probability tends to ZERO. Indeed, even for any q_j->0, eventually q_j^(-1)-1>=1 and log M_min >= 2^j log(1+1/j^2)->infinity.

This separation is a proved feature of a finite network family. It is NOT a claimed embedding of those networks into the odd Burnside action. Including arbitrarily many longer walks in this corridor cannot improve the whole-path minimum: every such support contains a simple corridor path support, and replacing it with that subset decreases every pairwise kernel entry. Duplicate copies merely aggregate weights.

There is no conflict with the earlier second-moment theorem: its bound was sufficient and not asserted optimal. The new proof controls the union of failed local cuts instead of the variance of a count of whole long paths.

## 7. Actual near-cost-one seeds in the target Bernoulli action

### Theorem 7.1

For every countable nonamenable group Gamma, its atomless-base Bernoulli action has nested subrelations (S_t)_{0<=t<=1} with

    C(S_t)=1+t,
    S_t ergodic,
    C(S_t|Y, normalized measure)=1+t/mu(Y)
           for every measurable Y with mu(Y)>0.       (7.1)

In particular S_t is nonhyperfinite on EVERY positive-measure restriction when t>0, although C(S_t) decreases to one.

Moreover, for 0<=s<=t<=1,

    relC(S_t;S_s)=t-s,                                (7.2)

and

    intersection_{t>0} S_t = S_0                     (7.3)

modulo null sets, with S_0 hyperfinite.

### Published inputs

[GL, Theorem 1] supplies, INSIDE the specified Bernoulli orbit relation R on [0,1]^Gamma, a free ergodic F_2 orbit subrelation Q. A free F_2 treeing has cost two [G,L]. [MT, Theorem 1.3] realizes the same ergodic treeable Q using free generators U,V with U (and even V) ergodic. These are full-group transformations of R, not asserted to be fixed elements of Gamma. Replacing generators does not change the ambient probability space or Q.

### Proof of the deductions

Choose an atomless measurable coordinate h:X->[0,1] with uniform distribution. Put A_t={h<=t}, with A_0 empty modulo null sets. Define

    S_t = relation generated by { U on X, V restricted to A_t }.

This graphing is a subgraph of the F_2 treeing. It is therefore a treeing, and its cost is exactly 1+mu(A_t)=1+t. The treeing-minimality theorem, not merely an upper bound, identifies this with C(S_t). Since U is ergodic and its relation is contained in S_t, S_t is ergodic.

Every positive-measure Y is consequently an S_t-complete section modulo null sets. The established induction formula [L, Proposition 2.33] gives

    C(S_t)-1 = mu(Y)[C(S_t|Y)-1],

which proves (7.1). Its classes are infinite because they contain U-orbits; positive-measure restrictions are aperiodic modulo null sets. A hyperfinite aperiodic relation has cost one. Thus the restrictions in (7.1) cannot be hyperfinite when t>0.

For (7.2), adjoining V only on A_t\A_s costs t-s and generates S_t from S_s. Conversely C(S_t)<=C(S_s)+relC(S_t;S_s), so the cost difference t-s is a lower bound. Hence equality.

For (7.3), remove the Q-saturation of the null set {h=0}. Two points in a Q-class have a unique tree path. If it uses a V-edge, that edge's starting point has positive h and is absent for all sufficiently small t. No alternative path exists inside the tree. Thus a pair survives every S_t exactly when its path uses only U-edges, meaning it is in S_0. QED.

### What is positive here, and what it does not provide

The low-cost, genuinely nonhyperfinite starting relations now have an ACTUAL construction in the target Bernoulli action. Their nonhyperfiniteness is not confined to a small exceptional region. This construction is a consequence of established theorems, not a claim to have newly resolved a known existence problem.

It does not ensure suitable connector probabilities or the network capacities of Theorem 4.1. Existence of such seeds alone cannot prove fixed price one: the construction also works when Gamma=F_2, whose Bernoulli action has cost two. In that example restoring S_1 from S_t costs exactly 1-t by (7.2).

Inside the original Q-tree, a missing V-edge also gives a literal capacity obstruction: remove that tree edge, partition the representatives of any certificate network by the two resulting sides, and every crossing edge-path must use its selection label. The load constraint then forces kappa<=1. To beat this obstruction in a larger ambient R, a construction must use genuine alternate R-paths, not merely rename paths in Q.

## 8. A precise constructive target after these results

Let Gamma=<a_1,...,a_r> be finitely generated and nonamenable. Work on its Bernoulli action. Choose low-cost seeds S_m (the S_t above are available choices, but not asserted optimal). Suppose for each generator a_j there are actual measurable network certificates on all but delta_{j,m} of the roots, with parameters v_{j,m}, L_{j,m}, kappa_{j,m} and numbers epsilon_{j,m} such that

    C(S_m)->1,
    sum_j [delta_{j,m}+epsilon_{j,m}
      +((4 log v_{j,m}+log(2/epsilon_{j,m}))/kappa_{j,m})^(1/L_{j,m})]
          ->0.                                      (8.1)

Then Theorem 4.1, joined over generators, gives Bernoulli cost one. By Abert–Weiss [AW, Corollary 2] and the infinite-action lower bound, Gamma has fixed price one.

For direct-edge certificates (L=1), a particularly transparent sufficient geometric target is kappa/log v -> infinity on almost all roots, with the error parameters chosen so log(1/epsilon)=o(kappa). This is a condition on GLOBAL weighted cuts after accounting for support reuse, not a count of paths and not an s-t cut alone.

No such family is constructed here for a large odd-exponent Burnside group. In particular, the finite corridor model is not asserted realized by these seeds, and the mere existence of torsion cycles is not asserted to imply large global capacity. That is the unproved step.

Universal Fixed Price also permits common costs above one; even a proof of this cost-one target for Burnside groups would not settle the universal statement. No critical-percolation sensitivity estimate is deduced here. Both original universal goals remain OPEN.

## 9. Verification and audit boundaries

The new finite replay uses exact fractions for fractional failure inequalities, cut-count bounds, completed finite cyclic-action graphings, and small corridor second moments. It separately evaluates the large-corridor formulas at high precision and solves finite illustrative capacity LPs numerically. Numerical LP and exponential evaluations are NOT exact assertions and are explicitly separated.

These checks do not verify Gaboriau–Lyons, Miller–Tserunyan, measurable finite-partition approximation, cost minimality, induction, infinite graphing costs, or the required Burnside certificates. Cairn checks artifacts and logical dependency bookkeeping, not mathematical truth. New ESTABLISHED labels denote asserted written deductions or published inputs; they are not formal proof certificates.

## References

[G] Damien Gaboriau, What is... cost?, arXiv:1011.2294v1. Definitions, treeing minimality, amenable cost and free-group cost. https://arxiv.org/html/1011.2294v1

[L] Damien Gaboriau, Lectures on Orbit Equivalence, Measure Equivalence and Cost. Proposition 2.33 (complete-section induction), Definition 2.38 and Proposition 2.39 (relative cost). Formula visually checked on PDF page 15. https://perso.ens-lyon.fr/gaboriau/Travaux-Publi/ME-Cost-L2-Lectures/ME-Cost-L2-lectures.pdf

[GL] Damien Gaboriau and Russell Lyons, A Measurable-Group-Theoretic Solution to von Neumann's Problem, arXiv:0711.1643v2, Theorem 1. https://arxiv.org/html/0711.1643v2

[MT] Benjamin D. Miller and Anush Tserunyan, Edge sliding and ergodic hyperfinite decomposition, arXiv:1704.06019v2, Theorem 1.3. We need ergodic generators, not a stronger assertion that every group element acts ergodically. https://arxiv.org/html/1704.06019v2

[F] Helmut Finner, A generalization of Holder's inequality and some probability inequalities, Annals of Probability 20(4) (1992), 1893–1901. The finite version needed in this note is reproved in Lemma 2.1. Bibliographic provenance verified through the primary paper [GLSS].

[GLSS] Dmitry Gavinsky, Shachar Lovett, Michael Saks, and Srikanth Srinivasan, A Tail Bound for Read-k Families of Functions, arXiv:1205.1478v1. Theorem 1.2 and the surrounding discussion explain the product-space dependence bound and cite Finner. https://arxiv.org/html/1205.1478v1

[K] David R. Karger, Random Sampling in Cut, Flow, and Network Design Problems, Mathematics of Operations Research 24(2) (1999), 383–413. Lemma 2.2 and Appendix A. The needed cut-count bound was visually checked on PDF page 7; our integer-parameter weighted proof is included. https://www.cs.cmu.edu/~avrim/Randalgs11/handouts/karger-random-sampling-mor-paper.pdf

[AW] Miklos Abert and Benjamin Weiss, Bernoulli actions are weakly contained in any free action, arXiv:1103.1063v2, Corollary 2 (finitely generated group Bernoulli maximality). https://arxiv.org/html/1103.1063v2

Previous conversation source: fixed-price-connector-capacity.md. Its adaptive finite-partition method motivates Section 4; its whole-path energy is compared in Section 6. No prior broad group-cost conclusion is assumed here.
