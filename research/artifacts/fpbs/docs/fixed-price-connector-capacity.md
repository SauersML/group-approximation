# Adaptive repair, overlap bounds, and a hyperfinite obstruction

Research continuation — September 9, 2026

## Status and scope

This note gives written proofs of (i) an adaptive, overlap-aware relative-cost bound, (ii) a variable-order torsion consequence, (iii) a regular-representation bound for hyperfinite subrelations, and (iv) a uniform obstruction to small average connector defects for hyperfinite subrelations of sufficiently large odd free Burnside groups. The last result also rules out hiding all the necessary nonhyperfiniteness on sets of vanishing measure.

No originality or priority claim is made. These are mathematical deductions with explicit proofs, not independently refereed or formally verified results. The finite replay checks finite identities and finite repaired connectivity only. Neither universal Fixed Price nor universal Benjamini–Schramm is solved, and no new low-cost Burnside subrelation realizing the final sufficient criterion is constructed here.

The two-generator and bounded-exponent conclusions of earlier conversation files are NOT premises of the new arguments. Earlier Cairn nodes remain in the package as provenance and have not all been re-audited.

## 1. Setup

Let a countable group Gamma act freely, probability-preservingly, on a standard probability space (X,mu). Remove an invariant null set and use right actions x -> xg. Let R be the orbit relation and S <= R a measurable subequivalence relation. Define

    Delta_S(g) = mu{x : not(x S xg)},
    relC(T;S) = inf{C(Psi) : S join R_Psi = T}.

All relation identities are modulo null sets. Cost is the sum of the domain measures of a graphing's partial p.m.p. maps; relation cost is the infimum over generating graphings. The added maps here are restrictions of a specified group transformation. Thus all their costs are accounted for directly, without any assertion about lengths of existing S-paths. Standard cost definitions and the infinite-class lower bound are recalled in [G].

The previous phase-repair note supplied a sufficient bound using small average defects along fixed disjoint torsion connectors. Here the repair can use different candidate paths at different roots, with arbitrary overlaps and arbitrary finite lengths.

## 2. Adaptive overlap-aware repair

Fix a in Gamma and q in (0,1). Before selecting any new edges, suppose that for almost every x we have measurably specified a nonempty finite family of valid finite paths from x to xa. A step of each path is either an S-connection or an unoriented a-edge {y,ya}. A reverse traversal still uses the a-edge whose starting point is y.

For candidate i let P_i(x) be the finite SET of starting points of a-edges required by the path. Repeated use of one edge is counted once. A path already in S can be assigned the empty support. The family size can depend measurably on x, and different roots need not choose group translates of the same path. All vertices belong to the orbit of x. The path list and weights are fixed before the auxiliary randomization.

Choose measurable weights w_i(x)>=0 with sum_i w_i(x)=1. Put

    K_q(x)_{ij} = q^(-|P_i(x) intersect P_j(x)|),
    M_q(x) = sum_{i,j} w_i(x) w_j(x) K_q(x)_{ij}.       (2.1)

### Theorem 2.1 (adaptive second-moment repair)

For every eta>0 there is a graphing Psi such that

    S join R_Psi = S join R_<a>,
    C(Psi) <= q + integral_X [1 - 1/M_q(x)] dmu(x) + eta. (2.2)

In particular M_q(x)>=1, and the eta-free right-hand side bounds the relative-cost infimum. The matrix K_q is positive semidefinite. The path family need not be disjoint, have uniformly bounded length, or arise from an exact subgroup relation.

### Proof

For a fixed root temporarily give the distinct points in the finite union of supports independent Bernoulli(q) labels. Let I_i be the event that every point of P_i is selected, and set

    Z_i = 1_{I_i}/q^|P_i|,
    W = sum_i w_i Z_i.

Then

    E Z_i = 1,
    E Z_i Z_j = q^{|P_i union P_j|-|P_i|-|P_j|}
                 = q^(-|P_i intersect P_j|).

Thus K_q is a Gram matrix, E W=1, E W^2=M_q, and M_q>=1. Since the weights are nonnegative, Cauchy–Schwarz gives

    1 = E[W 1_{W>0}] <= (M_q P(W>0))^(1/2).

At least one candidate is selected whenever W>0. Therefore

    P(no candidate selected) <= 1 - 1/M_q.               (2.3)

Now realize the needed estimate on the original probability space. Choose refining finite measurable partitions separating points. For almost every fixed x, the finitely many distinct points tested at x eventually lie in distinct atoms. Dominated convergence therefore gives a finite partition for which the set of roots with a tested collision has measure less than eta. This remains true for root-dependent points and a variable finite number of tested points. There is no uniform coding-radius assumption.

Temporarily select each atom independently with probability q, and let U be their union. The candidate families and weights do not change with these auxiliary colors. At every root outside the collision set the tested colors have exactly the independent law above. Let D(U) be the set of roots with no fully selected candidate. Then

    E_colors mu(U)=q,
    E_colors mu(D(U)) <= integral(1-1/M_q) dmu + eta.

By averaging, some deterministic measurable U has its SUM of selected and repair costs bounded by the right-hand side of (2.2).

Add T_a restricted to U and to D(U), or just to their union. On D(U) the direct a-edge is present. Else a valid candidate path is present. All a-connections are consequently generated; every new edge is itself an a-edge, so the joined relation is exactly S join R_<a>. The cost is at most mu(U)+mu(D(U)). This proves (2.2). QED.

### What is and is not optimized

One can minimize M_q over the finite probability simplex of weights. There is no need to assume a measurable exact minimizer: measurable near-minimizers can be chosen from countably many rational weight vectors, after partitioning by family size. The theorem also works with uniform weights, which avoids this issue entirely.

The second-moment bound is sufficient, not asserted optimal. It measures overlap of the NEW edges required by certificates. The lengths of paths already supplied by S do not enter, but a long candidate requiring many new a-edges is correctly penalized through the diagonal q^(-|P_i|).

### Corollary 2.2 (vanishing overlap penalty)

For each q in a sequence decreasing to zero, suppose there are finite candidate families and weights indexed by k with M_{q,k}(x)->1 almost everywhere. Then

    relC(S join R_<a>;S)=0.                               (2.4)

Indeed the integrand in (2.2) lies in [0,1], so dominated convergence gives relative cost <=q for each such q. Then let q go to zero.

More generally, for a finite generating set {a_1,...,a_r}, if subrelations S_m and valid families give numbers q_{j,m}>0 and matrices with

    C(S_m) -> 1,
    sum_j [ q_{j,m} + integral(1-1/M_{j,m}) dmu ] -> 0,    (2.5)

then C(R)=1. Choose summably small approximation errors for the finitely many repairs and join them to nearly optimal graphings of S_m. This is a sufficient construction criterion, not an equivalence or a proof that such S_m exist.

## 3. Exact overlap examples and unbounded orders

### Disjoint supports

If the k supports are disjoint and have sizes l_1,...,l_k>=1, then

    M_q = 1 + sum_i w_i^2(q^(-l_i)-1).

The optimizing weights are proportional to (q^(-l_i)-1)^(-1), giving

    min M_q = 1 + 1 / sum_i [q^l_i/(1-q^l_i)],
    1 - 1/min M_q = 1 / (1 + sum_i [q^l_i/(1-q^l_i)]).  (3.1)

For equal size l and uniform weights,

    M_q = 1+(q^(-l)-1)/k.                                (3.2)

This tends to one for fixed q as k increases. The earlier exact independence product is sharper in this special case; the present formula is designed to handle overlaps and adaptive choices as well.

### A shared bottleneck

If P_i={z,z_i}, with all z_i distinct and distinct from z, uniform weights give

    M_q = q^(-1)+(q^(-2)-q^(-1))/k.

This tends to q^(-1), not one. Indeed the exact success probability is

    q [1-(1-q)^k] -> q,

because every path needs z. Infinitely many candidate paths are not enough when they all require the same new edge. The formula detects this obstruction without an erroneous independence assumption.

### A variable-order torsion consequence

Let H<=Gamma, a in Gamma, and c_i=a b_i with b_i in H. Suppose c_i has finite order d_i>=2 and the power sets

    {c_i,...,c_i^(d_i-1)}

are pairwise disjoint. No common upper bound on d_i is imposed. If

    sum_i q^(d_i-1) = infinity for every q in (0,1),       (3.3)

then in EVERY free p.m.p. Gamma-action,

    relC(R_<H,a>;R_H)=0.                                  (3.4)

For the proof use the valid alternating cycle from the earlier torsion lemma: from xa take a b_i-step to xc_i, then selected a-steps and H-steps through powers of c_i, finally returning to x. Its support has size d_i-1. Formula (3.1) and (3.3) imply (2.4).

A sufficient growth condition is d_i=o(log i): for any fixed q>0, eventually q^(d_i-1)>=i^(-1/2). This gives an actual unbounded-order extension of the repair criterion, but no new concrete nonamenable fixed-price class is claimed solely from this condition.

## 4. Hyperfinite subrelations have regular-representation bounds

For S<=R put

    phi_S(g)=1-Delta_S(g)=mu{x:x S xg}.

Connection functions of this type are established objects in the positive-definite-function theory of subrelations [IKT]. The following bound is proved directly here.

### Proposition 4.1

If S is hyperfinite (an increasing union, modulo null sets, of finite-class subrelations), then for every finitely supported probability measure nu on Gamma,

    sum_g nu(g) phi_S(g) <= ||lambda_Gamma(nu)||_(2->2).   (4.1)

In particular the assertion holds for symmetric measures supported in any finitely generated subgroup.

### Proof for a finite-class subrelation F

On H=L^2(X x Gamma,mu x counting), define

    [Pi(g)f](x,h)=f(xg,g^(-1)h).

This is a unitary representation. The change of coordinates

    [Uf](y,h)=f(yh^(-1),h)

is unitary and satisfies

    U Pi(g) U^(-1)=I tensor lambda_Gamma(g).

Thus Pi is a direct sum (or Hilbert-space multiple) of the regular representation, regardless of the dynamics of the specified free action.

Let

    zeta_F(x,h)=1_{xh F x}/sqrt(|F[x]|).

Freeness makes the number of h with xh F x equal to |F[x]|, so ||zeta_F||=1. At a given x, the supports in h of zeta_F(x,h) and Pi(g)zeta_F(x,h) either coincide, with equal normalization, if x F xg, or are disjoint otherwise. Hence

    <zeta_F,Pi(g)zeta_F>=phi_F(g).

Taking the coefficient of Pi(nu) proves (4.1) for F.

If F_j increases to S, phi_Fj(g) increases to phi_S(g) for every g. Pass to the limit in the finite sum for nu. QED.

No Bernoulli-extension or independent-cluster-coloring assumption is needed. This bound applies to an arbitrary free action.

### Elementary defect inequalities

For EVERY subrelation S, not necessarily hyperfinite,

    Delta_S(g^(-1))=Delta_S(g),
    Delta_S(gh)<=Delta_S(g)+Delta_S(h).                    (4.2)

The second follows because x S xg and xg S xgh together imply x S xgh, and the distribution of xg is mu. Therefore for a word w of length at most L in u,v and their inverses,

    Delta_S(w)<=L max(Delta_S(u),Delta_S(v)).              (4.3)

## 5. A uniform hyperfinite barrier in odd Burnside groups

Fix Gamma=B(2,n), with n odd and sufficiently large that Osin's bounded-word embedding theorem holds. No numerical threshold is asserted for this combined use of results.

The external algebraic inputs are:

1. [O, Theorem 2.7]: there is L_n<infinity such that every noncommuting pair u,v in Gamma contains elements r,s of {u,v}-word length at most L_n that form a free Burnside basis of a subgroup isomorphic to B(2,n).
2. Nonamenability of the standard B(2,n) Cayley graph. Set

       rho_n = ||(lambda(a)+lambda(a^(-1))+lambda(b)+lambda(b^(-1)))/4|| < 1.

3. Every nonidentity centralizer in Gamma is cyclic of order n [O, Lemma 2.2; DS, Lemma 2.4].

Define

    epsilon_n=(1-rho_n)/L_n > 0.                          (5.1)

This is an existence constant, not a claimed evaluated numerical bound.

### Theorem 5.1 (all sufficiently reliable connectors lie in one finite cyclic group)

For every free p.m.p. Gamma-action and every hyperfinite S<=R,

    A_S={g:Delta_S(g)<epsilon_n}

is contained in a cyclic subgroup of order n. In particular |A_S|<=n.

### Proof

Suppose u,v in A_S do not commute. Obtain r,s from Osin's theorem. By (4.3),

    Delta_S(r)<L_n epsilon_n=1-rho_n,
    Delta_S(s)<1-rho_n.

But the regular representation of Gamma restricted to <r,s> is a sum of regular representations of that subgroup. Applying (4.1) to its symmetric four-point generating measure gives

    (phi_S(r)+phi_S(s))/2 <= rho_n,

or

    Delta_S(r)+Delta_S(s)>=2(1-rho_n),

a contradiction. Thus all elements of A_S commute pairwise. If A_S has a nonidentity element w, then A_S lies in C_Gamma(w), which is cyclic of order n. If it has none, its size is already at most one and it can be placed in any order-n cyclic subgroup. QED.

### Corollary 5.2 (uniform mean-defect obstruction)

For distinct b_1,...,b_k in Gamma,

    (1/k) sum_i Delta_S(b_i) >= epsilon_n(1-n/k).         (5.2)

Consequently every infinite sequence of distinct connectors satisfies

    liminf_k (1/k) sum_i Delta_S(b_i) >= epsilon_n.        (5.3)

At most n of the terms can be below epsilon_n; that proves the statements. The right side of (5.2) can be negative when k<n, in which case the inequality is simply uninformative.

The constant is uniform over the free action, the hyperfinite relation, and the chosen distinct connector list. Thus allowing S and the list to vary with an approximation parameter cannot make these averages tend to zero while S remains hyperfinite.

This does NOT prove that S of cost close to one must be hyperfinite. That implication is false in general, and is not used.

## 6. Nonhyperfiniteness cannot be hidden on a vanishing exceptional set

### Proposition 6.1

Let S<=R be arbitrary. Suppose Y is measurable with mu(X\Y)=delta and S restricted to Y is hyperfinite. Then for any k distinct connectors,

    (1/k) sum_i Delta_S(b_i)
       >= epsilon_n(1-n/k)-2delta.                        (6.1)

### Proof

Extend S|Y to all of X by singleton classes outside Y:

    E=(S intersect Y^2) union diagonal_X.

E is hyperfinite. An S-connection can disappear from E only if at least one endpoint is outside Y, so

    Delta_E(g)<=Delta_S(g)+2delta.

Apply (5.2) to E and rearrange. QED.

In particular, if an infinite distinct connector list for S has mean defect tending to zero, every hyperfinite restriction S|Y must satisfy

    mu(X\Y) >= epsilon_n/2.                              (6.2)

More generally a limiting mean defect at most e forces delta>=(epsilon_n-e)/2 whenever the latter is positive. This is a statement about deletion of measure, not a claim that an invariant nonamenable component of exactly that size exists.

Therefore the previous small-average-defect strategy cannot be implemented by hyperfinite subrelations, nor by putting all nonhyperfinite behavior on exceptional sets whose measures tend to zero. This rules out a specific construction strategy, not fixed price one for the group.

## 7. What remains a constructive route

There are now two DIFFERENT sufficient routes for the odd Burnside target:

(A) Construct target-action subrelations S_m of cost tending to one and connector families with average defects tending to zero, as in the previous note. Theorems 5.1 and 6.1 require such S_m to be genuinely nonhyperfinite in the quantitative deletion sense above.

(B) Use Theorem 2.1 instead: construct low-cost S_m and adaptive candidate paths with q_{j,m} plus their integrated overlap penalties tending to zero, as in (2.5). This need NOT make any fixed deterministic connector family nearly always available. Thus the hyperfinite mean-defect obstruction does not by itself rule out route (B).

Neither construction is supplied here. Both require actual paths and cost accounting inside the target Bernoulli action. A low-cost action on a different probability space is not substituted.

If either route achieved Bernoulli cost one for a finitely generated group, Bernoulli maximality [AW] and the infinite-action lower bound would give fixed price one. The currently published Burnside result [DS] proves infimal group cost one, explicitly not Bernoulli cost one. The present arguments do not remove that distinction.

The universal Fixed Price problem concerns equality of all free-action costs, including common values above one. A sufficient fixed-price-one criterion for one family is not a universal solution. Nothing here proves a universal near-critical pivotal bound or p_c<p_u for all nonamenable Cayley graphs.

## 8. Finite verification

`scripts/replay_connector_capacity.py` uses exact rational arithmetic. It checks:

- 575 finite support families, at three rational selection probabilities, verifying the overlap second moment and the probability bound;
- the exact optimizing-weight formula for disjoint supports and the common-bottleneck formulas;
- all 203 partitions of the regular six-point S_3 action, verifying finite-class representation coefficients and defect subadditivity;
- the two-endpoint deletion estimate for every subset of those finite spaces;
- adaptive torsion families depending on the root and on the arbitrary partition, with explicit repaired connectivity for 64,960 labelings.

These checks do not establish measurable selection on an infinite action, hyperfinite approximation, Osin's algebraic theorem, a Burnside spectral gap, or either conjecture. They are tests of the finite steps, not formal theorem verification. The precise counts are in `connector-capacity-checks.json`.

## References

[G] Damien Gaboriau, *What is... cost?*, arXiv:1011.2294v1 (2010). Used for standard definitions, infinite-action lower bound, and the distinction between cost one and amenability. The compression formula printed in that short note is not used in the new proof.
https://arxiv.org/html/1011.2294v1

[IKT] Adrian Ioana, Alexander S. Kechris, Todor Tsankov, *Subequivalence Relations and Positive-Definite Functions*, arXiv:0806.0430v1 (2008); Groups, Geometry, and Dynamics 3 (2009), 579–625. Context for the connection coefficient phi_S. Proposition 4.1 above is proved explicitly rather than attributed to an unlocated statement of [IKT].
https://arxiv.org/html/0806.0430v1

[O] Denis V. Osin, *Uniform non-amenability of free Burnside groups*, arXiv:math/0404073v1 (2004); Archiv der Mathematik 88 (2007), 403–412. Theorem 2.7 supplies bounded-word free-Burnside subgroups from noncommuting pairs; Lemma 2.2 supplies cyclic centralizers. We use these statements, not the stronger fixed universal-word assertion discussed only as an unproved announcement in the paper's remark.
https://arxiv.org/html/math/0404073v1

[AW] Miklos Abert and Benjamin Weiss, *Bernoulli actions are weakly contained in any free action*, arXiv:1103.1063v2 (2011), Corollary 2 for finitely generated groups.
https://arxiv.org/html/1103.1063v2

[DS] Miguel Donoso-Echenique and Eduardo Silva, *Free Burnside groups of large odd exponent have cost 1*, arXiv:2608.20472v1 (August 20, 2026). Theorem 1.2 and its following paragraph distinguish infimal cost one from fixed price one; Lemma 2.4 records cyclic centralizers.
https://arxiv.org/html/2608.20472v1

Prior conversation note: `fixed-price-phase-repair.md`, Sections 2–3. The new results do not assume its phase-normalization applications or earlier broad group-cost claims.
