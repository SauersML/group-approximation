# Finite-priority deletion and composite-order fixed-price-one groups

Research continuation — September 9, 2026

## Status and scope

This note gives written deductions, not an independently refereed or formally verified solution. Neither universal Fixed Price nor universal Benjamini–Schramm is proved. No originality claim is made.

The two additional results are: (1) a finite-priority deletion rule which preserves the entire generated equivalence relation while giving an integral bound on the retained-edge cost; (2) removal of primality from the preceding explicitly presented fixed-price-one family, using the published convex-embedding and connected-intersection lemmas of Gruber–Sisto. An explicit profile with unbounded even composite exponents is included.

The infinite-group assertions are proved using the cited mathematical inputs, not by the finite replay. Earlier broad bounded-exponent and two-generator claims are not premises. The cycle rule is related to classical minimal-spanning-forest methods [LPS]; the finite-valued implementation below supplies a direct proof of the measurable assertion needed here.

## 1. Definitions

Let a countable group Gamma act essentially freely and probability-preservingly on a standard probability space (X,mu). Restrict to an invariant conull free set, and write actions on the right, x -> xg. Let R be its orbit relation and S a measurable subequivalence relation.

A graphing is a countable family of partial p.m.p. bijections. Its cost is the sum of its domain measures. C(R) is the infimum over generating graphings. Put

    relC(T;S)=inf { C(Psi): S joined with R_Psi = T }.

The standard lower bound C(R)>=1 for aperiodic relations is imported from [G]. All graphings added below consist of restrictions of a specified transformation T_a. No graphing of exactly cost one is asserted to attain the infimum for a nonamenable group.

## 2. A deterministic finite-priority principle

Fix a in Gamma. For almost every x, suppose a finite family of paths from x to xa has been specified measurably. Each path uses existing S-connections and unoriented a-edges {y,ya}. A reverse traversal is charged to the starting point y of its underlying forward transformation. A candidate's support P_i(x) is the finite set of starting points of the required a-edges; repeated occurrences are counted once.

Only candidates whose support excludes x are useful for deleting the a-edge at x; discard the others. An empty support is allowed and certifies x S xa. The family itself may be empty. It is fixed before choosing priorities.

Let r:X->{1,...,M} be any measurable function with finite range. Retain the a-edge at x exactly when no candidate has all its support points strictly below x in priority:

    U_r={x: for every candidate i, some y in P_i(x) has r(y)>=r(x)}.

For an empty family this condition is true; for a candidate with empty support it is false.

### Lemma 2.1: exact preservation

    S joined with R_(T_a restricted to U_r) = S joined with R_<a>.

Proof. Induct on r(x). At the lowest priority, an a-edge can be deleted only using an empty support, so its endpoints are already S-connected. Suppose the connections for all smaller priorities have been recovered. If the edge at x is retained, it is directly available. Otherwise a candidate path uses only S-connections and a-edges of smaller starting-point priority. By induction each such edge is connected in the retained graphing. Substituting those finitely many paths recovers x to xa. There are only M priority levels. Thus every a-connection is recovered. Every added edge lies in R_<a>, giving the reverse containment as well. QED.

This is a finite induction, not a claim that an infinite descending chain of real priorities must terminate. There may be infinitely many roots and unbounded candidate lengths, but each root has finitely many finite candidates. A common conull set is obtained by removing the countable orbit-saturation of the exceptional null set.

## 3. Integral bound on the retained-edge cost

At a root x, assign independent Bernoulli(t) labels to the distinct points in the union of the candidate supports. Define

    f_x(t)=P(no candidate support is entirely selected).

Thus f_x(t)=1 for an empty candidate family and f_x(t)=0 when an empty support is present. These finite-network probabilities are measurable in x and polynomial in t, once the support incidence pattern is fixed.

### Theorem 3.1: finite-priority integral bound

For every eta>0 there is a finite-valued measurable priority function r such that U_r generates the a-connections above S and

    mu(U_r) <= integral_X integral_0^1 f_x(t) dt dmu(x) + eta.

Consequently,

    relC(S joined with R_<a>;S)
       <= integral_X integral_0^1 f_x(t) dt dmu(x).       (3.1)

Proof. Choose refining finite measurable partitions which separate points. For almost every x, the finitely many distinct tested points, including x itself, eventually lie in different atoms. Dominated convergence gives a finite partition whose collision-exception roots have measure below eta. This argument also works for root-dependent finite families and unbounded finite family sizes.

Assign independent uniform real priorities to the finitely many partition atoms. With probability one those atom priorities are distinct; replace them by their finite ranks, preserving all comparisons.

At a root outside the collision exception, condition on the original uniform priority t of its own atom. All other tested atoms have independent priorities, each lower than t with probability t. The root's a-edge is retained with probability f_x(t). Averaging over t, then x, gives

    E_colors mu(U_r) <= integral_X integral_0^1 f_x(t) dt dmu(x) + eta.

Some deterministic assignment of the finitely many ranks satisfies this upper bound. Lemma 2.1 proves generation for that assignment—and indeed for every finite assignment, even at collision roots. Let eta tend to zero in the cost infimum. QED.

No direct failure-repair domain is needed. An edge which does not have a certified lower-priority alternative is simply retained. The construction does not transfer an arbitrary source-action graphing to another action; S and the candidate paths must already be present in the specified target action.

### Comparison with selecting at one fixed density

For every t, f_x(t) is nonincreasing. Therefore, for any fixed q in [0,1],

    integral_0^1 f_x(t)dt <= q+(1-q) f_x(q).              (3.2)

The integral method is at least as good as the earlier union-of-selection-and-repair estimate using the same supports. This compares upper bounds, not optimal relative costs.

## 4. Exact torsion formulas

Let Gamma=<H,a>. Suppose b_1,...,b_k belong to H, c_i=a b_i has exact finite order d_i>=2, and

    P_i={c_i,c_i^2,...,c_i^(d_i-1)}

are pairwise disjoint. They exclude the identity.

At x, the reverse detour from xa to x is

    xa --b_i--> x c_i --a--> x c_i a --b_i--> x c_i^2
       --a--> ... --b_i--> x c_i^(d_i)=x.

Its b_i-steps belong to R_H and its required a-edge starting points are xP_i. Reversing this path yields the candidate needed in Section 2. Theorem 3.1 gives

    relC(R_Gamma;R_H) <= I(d_1,...,d_k),                (4.1)
    I(d_1,...,d_k)=integral_0^1 product_i(1-t^(d_i-1))dt.

For each positive tolerance, a restriction T_a|U of measure within that tolerance of I generates the whole action together with R_H.

If all d_i=d and L=d-1, the integral is exactly

    I_k(L)=integral_0^1(1-t^L)^k dt
          = product_{j=1}^k [Lj/(Lj+1)].               (4.2)

One proof integrates the derivative of t(1-t^L)^k to obtain

    (1+kL)I_k(L)=kL I_(k-1)(L),  I_0(L)=1.

Thus no numerical integration or special-function evaluation is needed for this bound.

For a uniform bound d_i-1<=L,

    I(d_1,...,d_k) <= I_k(L) <= k^(-1/L).               (4.3)

Indeed, (1-t^L)^k<=exp(-kt^L); integrating over [0,infinity) gives Gamma(1+1/L) k^(-1/L), and Gamma(1+1/L)<=1 by log-convexity of Gamma between 1 and 2. Alternatively, the exact product yields the same asymptotic estimate up to an explicit harmless constant. This analytic estimate is not needed for the exact fixed-price proof below.

For an infinite family, monotone/dominated convergence gives

    relC <= integral_0^1 product_{i>=1}(1-t^(d_i-1))dt. (4.4)

In particular, divergence of sum_i t^(d_i-1) for every t>0 forces relC=0. This is the same cost-one abundance hypothesis as before, but the finite-stage estimate is sharper and the deletion is certified by finite induction.

### A check against the earlier fixed-exponent Burnside bound

For B(2,n) with odd n>=1003, H=<b> has order n. The established cyclic-centralizer input [DS, Lemma 2.4] makes the n power sets for c_i=ab^i, 0<=i<n, disjoint. Each c_i has exact order n, as seen in the abelianization. (If two such order-n subgroups have a nonidentity common element, the two c_i lie in its cyclic centralizer and commute. Their quotient b^(j-i) then commutes with c_i, forcing c_i into <b>, a contradiction.)

Use a finite-group orbit treeing for H of cost 1-1/n, then (4.2):

    C(alpha) <= 1-1/n + product_{j=1}^n [(n-1)j/((n-1)j+1)]

for every free action. Exact rational arithmetic gives upper bounds, rounded UP,

    n=1003:  1.991558142683,
    n=10001: 1.998921726452.

These are upper bounds, not action-cost evaluations. This estimate does not approach one at a fixed exponent, and it does not determine the Burnside Bernoulli cost.

## 5. Primality is not needed in the explicit small-cancellation family

Choose ANY integers n_i>=13 for i>=1, and define

    G_n=<a,b | (a b^i)^(n_i)=1 for every i>=1>.          (5.1)

Assume

    sum_i t^(n_i-1)=infinity for every t in (0,1).        (5.2)

### Theorem 5.1

Every free p.m.p. action of G_n has cost one. The elements a,b have infinite order,

    ord(a b^i)=n_i,
    <a b^i> intersect <a b^j>={e} for i!=j,
    <a^2,b^2> is isomorphic to F_2.

No pairwise coprimality or primality of n_i is required.

The cost proof uses Sections 2–4. The additional algebraic input is [GS, Lemmas 2.15 and 2.17]: components of a Gr'(1/6)-labelled graph embed isometrically and convexly in the Cayley graph; images of two components have connected or empty intersection. The Gr condition allows label-preserving rotational symmetries and hence proper-power relators. The statements cover infinitely many finite relator components. These are imported theorems, not conclusions of the finite replay.

### 5.1 Small cancellation

Write u_i=ab^i and r_i=u_i^(n_i). Treat the symmetrized classical relators as a SET of distinct words. A common positive segment of distinct r_i,r_j, i!=j, has at most one a, because the lengths of b-runs between a's differ. Its length is at most 2 min(i,j)+1. Two distinct cyclic shifts of the SAME periodic relator have no a in their common prefix: aligning an a aligns the phase and makes the whole words equal, which has been excluded. The inverse cases are identical; positive and negative words share no letters.

Consequently every piece in r_i has length at most 2i+1, and

    2i+1 < n_i(i+1)/6.

This proves classical C'(1/6). Equivalently the disjoint union of the finite labelled relator circles is Gr'(1/6), with rotations by an entire period regarded as label-preserving automorphisms, as required in [GS].

### 5.2 Exact orders

Embed the circle labelled r_i into the Cayley graph with its basepoint at the identity, using [GS, Lemma 2.15]. The vertices at distances j(i+1) around this circle, 0<=j<n_i, map to u_i^j and are distinct. The relator gives u_i^(n_i)=e. Thus ord(u_i)=n_i exactly, without a prime-order argument.

### 5.3 Trivial intersections of the finite cyclic subgroups

Let C_i,C_j be the images of the two relator circles, both based at the identity. Their intersection contains the identity and its outgoing a-edge. By [GS, Lemma 2.17] it is connected. It cannot be a whole circle: an equality of circles as labelled subgraphs would equate the different b-spacings i and j. Hence the intersection is a path (a proper connected subgraph of a simple cycle).

As a common labelled path, it has at most one a-edge. To justify this independent of a chosen orientation, the directions on each positive relator circle are coherent; traversing a common path in either direction reads either only positive or only negative letters. Two a-edges on such a path would force the same intervening b-spacing in the two circles.

If a nonidentity element w belonged to <u_i> intersect <u_j>, then it would be a phase-zero vertex on BOTH circles. Its outgoing a-edge would lie in the intersection, in addition to the outgoing a-edge at the identity. These are distinct edges: a has infinite order, as proved just below, so an edge cannot be identified with its reverse. This contradicts the one-a-edge bound. Thus the cyclic subgroups have trivial intersection.

The infinite-order fact used in the last sentence does not depend on this argument: any nonzero power of a, or of b, has no relator-half subword, so it follows immediately from Greendlinger's lemma [S, Theorem 3.7]. Equally, directed a-edges starting at different vertices are already distinct in the labelled Cayley graph.

### 5.4 Nonamenability

Substitute A=a^2, B=b^2 into a nonempty cyclically reduced word in abstract free generators A,B. All its a-runs and b-runs have even length. A subword matching r_i or r_i^(-1) cannot pass through an internal a-run, because all a-letters of r_i are isolated. A match therefore has length at most i+2 (at most two a-letters, at its ends, surrounding one b-run). This is less than n_i(i+1)/2.

The substituted cyclic word cannot contain more than half a relator and is nontrivial by Greendlinger's lemma [S]. Thus <a^2,b^2>=F_2 and G_n is nonamenable. In particular the group is infinite.

### 5.5 Cost

For an arbitrary free action, keep T_b on all of X, at cost one. The distinct cyclic subgroups above supply disjoint supports of sizes n_i-1. Equation (4.1) supplies, for each finite k and eta>0, a restriction T_a|U such that the pair generates the entire action and

    C({T_b,T_a|U}) <= 1 + integral_0^1 product_{i<=k}(1-t^(n_i-1))dt + eta.

By (5.2), the product tends to zero at each t>0. Dominated convergence makes the integral tend to zero. Taking infima gives C(alpha)<=1; the infinite-class lower bound gives equality. This holds in every specified free action, without an ergodicity assumption or a Bernoulli-extension substitution. QED.

## 6. A simple explicit unbounded-composite profile and its rate

Take natural logarithms and put

    n_i = 16 + 2 floor(sqrt(log(i+1))).                         (6.1)

All exponents are even and composite, at least 16, and tend to infinity. Since n_i=o(log i), for each fixed t>0 one eventually has t^(n_i-1)>=i^(-1/2). Thus (5.2) holds.

For this explicit group, every free action has cost one, and the specified elements ab^i have exact unbounded composite orders. It also contains the explicit free subgroup <a^2,b^2>.

For the first k relations, put L_k=15+2 floor(sqrt(log(k+1))). Then n_i-1<=L_k for i<=k, and (4.3) gives an actual generating graphing, for each eta>0, with

    C <= 1 + k^(-1/L_k) + eta.                                (6.2)

The excess in this constructive bound decays at least as

    exp(-(1/2+o(1)) sqrt(log k)).                              (6.3)

Here k is the number of detours used, not a group exponent or graphing path-length bound. The partition needed to implement the priorities can be extremely large. No efficiency or uniform coding radius is asserted for arbitrary actions.

## 7. Optional combination with the earlier cut bound

The priority theorem also integrates a valid rootwise cut-reliability estimate. This is not needed for Theorem 5.1.

Suppose network certificates from the preceding cut note have v vertices, path-support sizes <=L, and fractional global cut capacity at least kappa. Remove all network edges whose support contains the root x. The fractional load at x is at most one, so every cut loses at most one unit: the remaining capacity is at least K=kappa-1. This removal is necessary before comparing other priorities with the root priority.

Assume K>0 and set c=4 log v+log 2. For t>=(c/K)^(1/L), the earlier cut estimate bounds disconnection by 2 v^4 exp(-K t^L). Every selected network route supplies a candidate avoiding the root edge. Integrating Theorem 3.1 gives, outside a root exception of measure delta,

    relC <= delta + (c/K)^(1/L) * (1+1/(L c)),                 (7.1)

provided c/K<1. For the tail integral, substitute u=Kt^L and use u^(1/L-1)<=c^(1/L-1) for u>=c. The factor 2v^4 exp(-c) is one.

For L=1 this is delta+(4 log v+log 2+1)/(kappa-1). Unlike a single chosen threshold estimate, it needs no separate failure-tolerance parameter. It still requires actual certificates with large capacity inside the target action. None is constructed for an arbitrary group here.

## 8. Percolation and the universal gaps

By [GS, Theorem 1.3], these classical C'(1/6) groups are virtually cyclic or acylindrically hyperbolic. They contain F_2, so the latter alternative holds. By [CS], every locally finite Cayley graph of each such group has p_c<p_u. This percolation assertion is an application of existing theorems, not a new universal percolation proof.

The universal Fixed Price problem asks for equality across arbitrary actions of EVERY infinite countable group, including common values above one. Our explicit presentations are chosen to have infinitely many separate torsion detours; arbitrary groups need not have these. The fixed-exponent odd Burnside upper bound in Section 4 still does not reach one. Neither the universal graphing-transport theorem nor a universal near-critical pivotal estimate has been established.

Finite priority values certify every finite construction. Passing to a numerical limit of the costs does not assert that a single limiting graphing is generating. This distinction is essential.

## 9. Verification scope

The executable script `scripts/replay_priority.py` passes 51,532 exact assertions. It tests 25,984 binary-priority cases (including ties) across all 203 partitions of a regular S3-action and two generator types, plus 17,280 all-distinct-priority cases on selected partitions. In these finite models, the candidate torsion cycles depend on the root and on an arbitrary finite subrelation, and may overlap. Every deletion preserves the original generated relation.

It also counts 11,102 rooted priority permutations for 10 disjoint-support profiles, checks 600 exact integral/product identities, and verifies 3,828 pairs of distinct symmetrized words in a nonprime-exponent sample. The numerical Burnside entries are exact rational products rounded upward, not unconstrained floating-point estimates.

These checks do not prove measurable approximation, cost lower bounds, infinite small cancellation, convex embedding, connected intersections, or either universal conjecture. The script tests finite calculations only. No Cairn compilation result should be understood as independent mathematical verification.

## References

[G] Damien Gaboriau, *What is... cost?*, arXiv:1011.2294v1. Standard definitions and the infinite-action lower bound. https://arxiv.org/html/1011.2294v1

[LPS] Russell Lyons, Yuval Peres, Oded Schramm, *Minimal spanning forests*, Annals of Probability 34 (2006), 1665–1692; arXiv:math/0412263v5. Context for priority-based cycle deletion; the finite-priority implementation used here is proved explicitly above. https://arxiv.org/abs/math/0412263

[GS] Dominik Gruber, Alessandro Sisto, *Infinitely presented graphical small cancellation groups are acylindrically hyperbolic*, arXiv:1408.4488v3. Lemmas 2.15 and 2.17 (isometric convex embedding, connected intersections); Theorem 1.3 (classical C(7)). Its Gr conditions explicitly allow nontrivial label-preserving automorphisms and torsion. https://arxiv.org/html/1408.4488v3

[S] Mark Sapir, *Asymptotic invariants, complexity of groups and related problems*, arXiv:1012.1325v4, Theorem 3.7 (classical Greendlinger lemma). https://arxiv.org/html/1012.1325v4

[DS] Miguel Donoso-Echenique, Eduardo Silva, *Free Burnside groups of large odd exponent have cost 1*, arXiv:2608.20472v1, Lemma 2.4 (cyclic centralizers). The paper's group-cost conclusion is infimal cost, not fixed price. https://arxiv.org/html/2608.20472v1

[CS] Inhyeok Choi, Donggyun Seo, *Percolation in acylindrically hyperbolic groups*, arXiv:2508.08932v2. https://arxiv.org/abs/2508.08932

Prior conversation files: `fixed-price-small-cancellation-family.md` (prime-exponent family and single-threshold repair); `fixed-price-cut-repair.md` (finite correlated-cut estimate used only in Section 7).
