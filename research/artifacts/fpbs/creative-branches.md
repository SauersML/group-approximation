# Creative research branches: pivotal sensitivity, cluster wavelets, and sparse spines

Date: 2026-09-08 (America/Chicago).

## Scope and epistemic status

This is a research proposal with proved conditional reductions and exact elementary identities, not a solution of either universal conjecture. The universal pivotal estimate, a dyadic operator estimate, the proposed Kazhdan-group sparse-spine statement, and the positive-rank-gradient construction are OPEN. No claim of mathematical priority is made. Known theorems are explicitly attributed below. Numerical/exhaustive checks concern finite algebra, not infinite conjectures.

We work with simple, locally finite Cayley graphs of finitely generated infinite groups unless explicitly stated otherwise. The universal Fixed Price question also includes countable groups not finitely generated; the positive constructions below do not silently claim that additional generality.

## 1. Pivotal sensitivity rather than shortest-path length

Let G be nonamenable, of degree d. Let X_n be simple random walk on G from o, independent of percolation, and let rho=||P||_{2->2}<1 be its spectral radius. Define

    a_n(p)=P_p(o connected to X_n).

Schramm's lemma gives a_n(p_c)<=rho^n [S,H]. A lazy walk can also be used: average the simple-walk bounds over a binomial number of steps and replace rho by (1+rho)/2.

### 1.1 The finite-volume Russo identity

Let R>=n and let E_{n,R} be the event that o and X_n are connected in the percolation restricted to the induced ambient ball B_R. Write a_{n,R}(p)=P_p(E_{n,R}). On this event let N_{n,R} count the open edges whose deletion destroys that connection. Thus these are pivotal edges, not all edges of a selected path.

Condition on X_n and apply Russo's formula in the finite edge set. Whether an edge is pivotal is independent of its own state. For an increasing event, an open pivotal edge implies the event. Consequently

    p a'_{n,R}(p) = E_p[N_{n,R} 1_{E_{n,R}}],

and hence, for 0<p<1,

    d/dp log a_{n,R}(p)
       = E_p[N_{n,R} | E_{n,R}]/p.                      (P1)

This is an identity of finite polynomials before division. No assertion about differentiating an infinite-volume event is needed.

### 1.2 A precise sufficient estimate

**Open pivotal-budget hypothesis for G.** There are constants C>0 and p_0 in (p_c,1) such that, for all n>=1, all R>=n and all p in [p_c,p_0],

    E_p[N_{n,R} | E_{n,R}] <= C n.                     (P2)

**Conditional theorem.** If (P2) holds, then

    p_c < p_u,

and every p with

    p_c < p < min{p_0, p_c rho^(-1/C)}

is in the nonuniqueness phase.

**Proof.** Integrating (P1) gives

    a_{n,R}(p) <= a_{n,R}(p_c) (p/p_c)^(Cn)
                  <= [rho (p/p_c)^C]^n.

Let R tend to infinity, using increasing finite-volume connection events. If rho(p/p_c)^C<1, then a_n(p) tends to zero with n. On the other hand, uniqueness at a supercritical p implies, by FKG,

    P_p(x connected to y) >= theta(p)^2

for all x,y, and therefore a_n(p)>=theta(p)^2>0. This is a contradiction. Supercritical transitive Bernoulli percolation has either one or infinitely many infinite clusters, giving the conclusion. QED.

The hypothesis's uniformity in R and its validity on an interval *above* p_c are load-bearing. Critical finiteness and Schramm's lemma alone do not imply (P2). The condition is sufficient; we have not proved that it is necessary for nonuniqueness or that it is strictly weaker than every L2 approach.

### 1.3 Why the previous routing obstruction does not rule this out

Take the earlier model H_epsilon on T_{2r} square Z: retain all vertical edges and each horizontal edge independently with probability epsilon>0. Its expected shortest-path distance across one horizontal generator is

    E D_epsilon=(2-epsilon^2)/(epsilon(2-epsilon)) ~ 1/epsilon.

**Elementary additional observation. Every edge of H_epsilon lies on a finite cycle, almost surely.**

For a retained horizontal edge across neighboring vertical fibers, there is another retained horizontal edge between those fibers at another height. These two edges and the vertical segments make a rectangle.

For a vertical edge from height k to k+1 in a fiber, fix one neighboring fiber. Almost surely there are retained horizontal crossings between the fibers both at a height at most k and at a height at least k+1. The resulting rectangle contains the chosen vertical edge. The assertion holds simultaneously for all edges by countability.

Thus H_epsilon has no bridges. In a connected graph an edge is pivotal for the connection of some pair only if it is a bridge. So the pivotal count between any two vertices of H_epsilon is zero, while its shortest replacement paths can be arbitrarily long on average.

This model is dependent/anisotropic and is NOT a proof of (P2) for Bernoulli percolation. It establishes the conceptual separation: long paths need not entail many indispensable edges. In finite balls artificial boundary bridges can appear; the infinite no-bridge statement must not be substituted for the uniform finite-volume requirement in (P2).

### 1.4 Structural pilot classes

On a tree, conditional on connection, N_{n,R}=d_G(o,X_n)<=n, so C=1 works for every p. More generally, suppose the graph is assembled from finite blocks meeting at cutvertices in a tree pattern and every block has at most b edges. Every connection follows the unique block chain between its endpoints. Pivotal edges are confined to this chain. The chain has at most d_G(x,y) blocks, since every traversed block contributes at least one step to a shortest path. Thus N_piv(x,y)<=b d_G(x,y), including in induced finite balls whenever a connection exists. Hence C=b is a deterministic bound. These are checks in already tractable geometries, not newly solved universal cases.

For graphs without such a block decomposition, contract the open components that remain after deleting bridges. Pivotal distance is distance in the resulting bridge tree, not distance inside the potentially huge bridge-free pieces. The proposed research task is an annealed bound on this bridge-tree distance for random-walk endpoint pairs. Finite-volume boundary effects and conditioning on a rare connection must be retained throughout.

## 2. Replace the false inverse-sign lemma by a positive merger calculus

For a finite percolation configuration omega with clusters C, define the cluster-averaging projection

    P_omega(x,y)=1{x,y in the same cluster}/|C_x|.

It is an orthogonal projection: on each cluster it replaces a function by its mean.

### 2.1 Exact rank-one identity

Suppose opening one edge merges disjoint clusters A,B with sizes a,b. Put

    w = 1_A/a - 1_B/b,
    u = sqrt(ab/(a+b)) w.

Then ||u||_2=1, and direct block-matrix calculation gives

    P_before - P_after = u u*.                         (Q1)

Indeed the A-A block of the difference has coefficient b/[a(a+b)], the B-B block has coefficient a/[b(a+b)], and the two cross blocks have coefficient -1/(a+b). These are exactly the blocks of u u*.

Thus projections decrease in positive-semidefinite order as clusters merge. In a finite monotone percolation history, the rank-one differences at different merger times are mutually orthogonal: their ranges are the successive orthogonal differences of nested projection ranges. They form a hierarchical Haar basis for the functions with zero mean on each final cluster:

    I - P_final = sum_over_mergers u u*.

The trace counts merges but discards the directions u. This gives a concrete reason scalar cluster counts lose information that an operator approach might retain.

This does not say that the inverse connectivity matrix is a graph Laplacian. The four-cycle counterexample still gives (T^{-1})_{0,2}=16/1845>0 at p=1/2.

### 2.2 Dyadic large-cluster projections

At criticality in a nonamenable Cayley graph the clusters are finite almost surely [CF]. For k>=0 let P_{omega,k} average on the clusters of size in [2^k,2^(k+1)), and be zero on all other clusters. Define Q_k=E[P_{omega,k}]. Each Q_k is a positive contraction, with kernel

    Q_k(x,y)=E[1{x connected to y, 2^k<=|C_x|<2^(k+1)}/|C_x|].

For any finitely supported f,

    <f,T_pc f>
      = E sum_C |sum_{x in C} f(x)|^2
      <= sum_{k>=0} 2^(k+1) <f,Q_k f>.

Therefore the open estimate

    sum_{k>=0} 2^k ||Q_k||_{2->2} < infinity             (Q2)

would prove boundedness of T_pc and hence Benjamini-Schramm via [H]. A concrete stronger target is

    ||Q_k||_{2->2} <= C 2^(-(1+eta)k), eta>0.           (Q3)

Neither (Q2) nor (Q3) has been proved here universally. In particular, writing the desired operator bound in this form is a research reduction, not a solution. (Q2) is sufficient and is not asserted equivalent to boundedness of T_pc.

### 2.3 Independent-cluster overlap as an intermediate observable

Let C and C' be independent root clusters at p_c. Then

    <delta_o,Q_k^2 delta_o>
      = E[1{C,C' both in shell k} |C intersection C'|/(|C||C'|)].

This is an exact consequence of composing the two independent cluster projections. Higher powers involve chains of such intersections. A possible approach is to use expansion plus the cancellation in (Q1) to control these chains uniformly over test vectors.

A single root-overlap bound is NOT an operator-norm bound. It controls a trace moment, and rare or highly aligned spectral directions may still matter. Any completed proof must address that distinction.

### 2.4 An equivalent ghost-regularity formulation (not independent evidence)

Let Q(t) average on each finite critical cluster with the extra weight e^(-t|C|), with Q(0)=E P_omega. Then

    [Q(0)-Q(t)]/t
      = E[(1-e^(-t|C|))/(t|C|) 1{same cluster}].

As t decreases to zero, these positive quadratic forms increase to T_pc. Thus a uniform Lipschitz estimate

    ||Q(0)-Q(t)|| <= M t

is equivalent to boundedness of T_pc. This formulation may permit a positive-operator proof, but as an equivalence it is not a weaker solved substitute for the L2 conjecture.

## 3. Sparse connected spines for the fixed-price-one branch

A factor of iid (FIID) construction is a measurable translation-equivariant function of independent vertex labels. This admissibility matters: an arbitrary invariant construction gives a bound for some action, not automatically the Bernoulli action of maximal cost [AW].

**Sparse-spine lemma.** Suppose an FIID vertex set I is almost surely nonempty, infinite and connected in G, with theta=P(o in I). Then

    C*(Gamma) <= 1+(d/2-1)theta.                        (F1)

**Proof.** Retain every ambient edge with both endpoints in I. For each vertex outside I choose one neighboring vertex whose ambient distance to I is one less, breaking ties using additional iid labels. No root of I is chosen. Every outside vertex reaches I after finitely many steps, so the resulting spanning graph is connected. The outside parent edges have intensity exactly 1-theta: there is one directed edge per outside vertex and no opposite pair, since height decreases. Internal I-edges have intensity at most d theta/2. This proves (F1) for a graphing of a free Bernoulli action. Bernoulli maximality gives the bound for C*. QED.

Consequently, arbitrarily small-density FIID connected infinite spines prove fixed price one.

A serious restricted target is whether all infinite property-(T) groups admit such spines. This is OPEN here and must not be treated as a consequence of their known minimum cost one. It would give fixed price one for that class, not all countable groups or groups whose price exceeds one.

The creative construction idea is to use overlapping infinite cells with repeated opportunities for contact, not globally constant random colors on whole infinite components. Recent product-group proofs exploit infinite semi-touching/horoball geometry and carefully preserve weak-FIID admissibility [K]. The product-neighbourhood criterion [PN] supplies another concrete benchmark:

    |F_n S F_n^{-1}|/|F_n|^2 -> 0  implies fixed price one.

This implication is published; we are not claiming that every fixed-price-one group satisfies its hypothesis, nor that it settles percolation for those groups.

### 3.1 Connectivity certificates without uniformly short routes

For a connected countable graph, let E_0 be retained edges and give every deleted edge a positive integer level. Suppose a deleted edge of level m has a finite alternate path using only E_0 and deleted edges of levels less than m. Induction on m shows that its endpoints are connected using E_0 alone. Therefore E_0 is connected.

This elementary well-founded replacement lemma permits arbitrarily long routes, while preventing connectivity from disappearing in a limit of cycle deletions. The missing quantitative task is to design such certificates while achieving a desired low edge intensity in an admissible Bernoulli construction. The lemma alone does not provide that sparsification.

## 4. Keep a falsification branch: property (T) plus positive Farber rank gradient

Hutchcroft-Pete proves that every infinite property-(T) group has minimum action cost one [HP]. Abert-Nikolov proves, for a Farber chain Gamma_n of finite-index subgroups,

    Cost(boundary action) = 1 + lim_n (d(Gamma_n)-1)/[Gamma:Gamma_n].

Thus an infinite residually finite property-(T) group with a Farber chain of positive rank gradient would refute Fixed Price. No attainment assumption for minimum cost is needed: minimum/infimum one supplies an action whose cost is strictly below the positive-gradient boundary action.

A concrete sufficient certificate is a prime ell and

    liminf_n dim_Fell H_1(Gamma_n;Fell)/[Gamma:Gamma_n] > 0,

since d(Gamma_n) is at least this homology dimension. A proposed construction must simultaneously maintain property (T), essential freeness of the profinite boundary action (e.g. a normal chain with trivial intersection), and this genuinely positive asymptotic lower bound. Large homology at finitely many levels, a non-Farber chain, or a weighted presentation deficiency alone supplies none of those missing implications. No such group or chain is constructed here.

## 5. Priorities and validation

The lead experiment is the pivotal-budget program: it asks for sensitivity of connectivity rather than uniform path geometry, and its conditional implication can be proved using finite-volume calculus. The projection program offers a positive multiscale language that avoids the false inverse-sign lemma. Sparse spines provide a sharply formulated constructive objective for fixed-price-one classes. The rank-gradient branch prevents assuming the conjecture's answer in advance.

The replay script verifies 64 exact rank-one merger identities and 150 exact finite Russo polynomial identities across 344 edge configurations on seven small graphs, and reproduces the four-cycle inverse entry. None tests the universal estimates.

## References

[S] Gady Kozma, Percolation on a product of two trees, Ann. Probab. 39 (2011), 1864-1895, introduction and Schramm's lemma. https://arxiv.org/html/1003.5240v3

[H] Tom Hutchcroft, Percolation on Hyperbolic Graphs, Proposition 6.4 and the operator criterion. https://arxiv.org/html/1804.10191v3
Also: The L2 boundedness condition in nonamenable percolation. https://arxiv.org/html/1904.05804v2

[CF] Benjamini-Lyons-Peres-Schramm, Critical percolation on any nonamenable group has no infinite clusters (1999). Discussion and references in Hutchcroft, Locality of the critical probability for transitive graphs of exponential growth. https://arxiv.org/html/1808.08940v2

[AW] Miklos Abert and Benjamin Weiss, Bernoulli actions are weakly contained in any free action, Corollary 2. https://arxiv.org/html/1103.1063v2

[K] Ali Khezeli, Products of Infinite Countable Groups Have Fixed Price One. https://arxiv.org/html/2509.08325

[PN] A Product-Neighbourhood Criterion for Fixed Price One, arXiv:2607.20273v1, Theorem 1.1. https://arxiv.org/html/2607.20273v1

[HP] Tom Hutchcroft and Gabor Pete, Kazhdan groups have cost 1. https://arxiv.org/html/1810.11015

[AN] Miklos Abert and Nikolay Nikolov, Rank gradient, cost of groups and the rank versus Heegaard genus problem, Theorem 1. https://arxiv.org/html/math/0701361v3
