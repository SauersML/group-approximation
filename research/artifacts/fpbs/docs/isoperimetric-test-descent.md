# Descending isoperimetric tests for a pulled-back graphing

September 10, 2026. A written deduction using approximate measurable
edge coloring. This is not a resolution of Fixed Price. No priority,
referee verification, or Lean verification is claimed.

## 1. Statement and conventions

Let a countably infinite group Gamma act essentially freely and pmp
on standard probability spaces (Y,nu) and (X,mu). Let pi:Y->X be an
equivariant measure-preserving factor map. Assume the base action
is ergodic. Write R_Y,R_X for the orbit relations. Work on invariant
conull Borel sets on which the actions are free, using left actions.

Let K be a simple unoriented Borel graphing of R_X with degree at
most d<infinity. Its lift K^pi has an edge between y and gy when
K has the edge between pi(y) and g pi(y). Freeness makes pi an
isomorphism from each individual lifted orbit graph to its base
orbit graph.

For n full-group maps theta_1,...,theta_n with pairwise disjoint
graphs, put A_x={theta_1(x),...,theta_n(x)} and define

    b_K(A) = integral_X |boundary_K A_x| dmu(x),
    h_K(R_X) = inf_(n,A) b_K(A)/n.                         (1)

Edges of the boundary are counted once. The full group [R_X]
consists of pmp Borel bijections whose graphs lie in R_X; disjoint
graphs mean distinct images at almost every x. Define the source
constant by allowing all such maps on Y, including ones that do
not descend to X.

**Theorem.** Under these hypotheses,

    h_(K^pi)(R_Y) = h_K(R_X).                              (2)

The graphing in (2) must be supplied by the base. It may not
depend on the forgotten coordinate.

Definition (1) is the symmetric-vertex definition of
[Lyons--Pichot--Vassout, Section 4.4](https://arxiv.org/pdf/0711.0393).
For ergodic finite-cost relations,
[Pichot--Vassout](https://arxiv.org/pdf/0903.0911)
identify inf_K h_K(R) with 2(C(R)-1).

## 2. Two measurable repair facts

**Approximate edge decomposition.** If S is a Borel subset of
R_X with outgoing and incoming degrees at most N, then after
removing arbitrarily small pair measure it is the disjoint union
of N partial pmp bijection graphs. Pair measure means
m(S)=integral |S_x| dmu, also the integral of incoming degrees.

Apply [Grebik, Theorem 1.2(I)](https://www.numdam.org/item/10.5802/ahl.124.pdf)
to the bipartite graph on two copies of X with edges S, giving
each copy measure one half. Its maximum degree is at most N.
Choose an N-coloring with incorrect vertices of measure less
than eta/(2N), and remove all incident edges. The removed pair
measure is less than eta by the degree bound and pmp property.
Color classes are partial bijections, and they preserve measure
because their graphs lie in R_X. Append empty colors if necessary.

**Completion with exclusions.** A partial pmp bijection f in R_X
extends to a full-group map avoiding a finite list of other
partial-bijection graphs on the added domain. Assume its existing
part already avoids that list.

Let U,V be the complements of its domain and range; mu(U)=mu(V).
Enumerate Gamma and greedily add every available restriction of
each group map between unmatched U and V points, excluding
forbidden pairs. The union is a partial pmp bijection. Its two
residual sets U',V' have equal measure and no allowed pair between
them: any pair between final unmatched endpoints was available
when its group element was processed. If this common measure
were positive, almost every x in U' would have infinitely many
R_X-related points in V', of which only finitely many are forbidden.
This contradicts the absence of an allowed pair.

The recurrence assertion follows using an ergodic aperiodic
T in [R_X]: almost every T-orbit visits any positive-measure
set infinitely often. Existence of such T for ergodic type II_1
relations is standard and is also used in Section 3 of
Pichot--Vassout. Thus the extension is full modulo null sets.

In particular, N disjoint partial-bijection graphs extend to N
disjoint full-group graphs. Extend successively, forbidding all
previously extended graphs and all later original partial graphs.
Total pair measure added is N minus the measure of the original
union. These constructions take place on X itself.

## 3. Project a source test to a kernel of finite sets

Take disjoint theta_1,...,theta_n in [R_Y] and put

    P_y={pi(theta_j(y)):1<=j<=n},
    B=integral_Y |boundary_K P_y| dnu(y).

Projection preserves the n distinct points and the boundary, so
the source ratio is B/n. Write theta_j(y)=g_j(y)y measurably.
Choose finite D subset Gamma such that all g_j(y) lie in D
except on an event of probability at most epsilon. Replace P_y
by the empty set on that event, obtaining P_y^D. Then

    integral (n-|P_y^D|) dnu <= n epsilon,
    integral |boundary_K P_y^D| dnu <= B.                  (3)

Condition on X. The law Q_x of P_y^D is a measurable probability
kernel on the finitely many displacement subsets of D, with each
realized set either empty or of size n. Its incoming marginal is

    a(z)=sum_(g in D) Q_(g^(-1)z){P:z in P} <= n a.e.     (4)

For verification, before truncation let
p_(j,g)(x)=E[1_{g_j(y)=g}|pi(y)=x]. Since pi composed with theta_j
sends nu to mu, change variables by each group element to get
sum_g p_(j,g)(g^(-1)z)=1 almost everywhere. Sum over j and use
disjointness. Truncation only decreases this marginal. Tonelli
justifies the nonnegative sums. No coherent selection of a source
point above each base point is asserted.

## 4. Average the kernel

Sample m independent uniform numbers u_i and use a common Borel
inverse-distribution rule to obtain P_i(x)=P(x,u_i) with law Q_x.
These numbers only prove existence of a deterministic finite
list of measurable set assignments on X; they are not a new
dynamical factor.

Set L=|D|, N=mn and b_i(z)=#{x:z in P_i(x)}. Every such x is
g^(-1)z for g in D, so b_i<=L. For each z these variables are
independent across i and have mean a(z)<=n. Consequently

    E integral (sum_i b_i-N)_+ dmu <= L sqrt(m),           (5)

by the variance bound and Cauchy--Schwarz. Set
t_i=integral |P_i(x)| dmu and q_i=integral |boundary_K P_i(x)| dmu.
Equations (3)--(5) imply that for any eta>0 there is a deterministic
list satisfying

    sum_i q_i + d sum_i(n-t_i)
       +2d integral (sum_i b_i-N)_+
       <= mB + dmn epsilon + 2dL sqrt(m) + eta.            (6)

The eta avoids requiring attainment of an expectation bound.
Independence across sample indices suffices; none is needed
across different roots in an orbit.

## 5. Separate the sets and restore balance

Replace P_i(x) by P_i(T^(k_i)x), using the T from Section 2.
This preserves t_i,q_i by measure preservation. It preserves b_i
pointwise because T^(k_i) permutes each orbit. All sets still lie
in the same orbit graph as x.

Choose powers successively so that overlap losses total at most
eta. Indeed, for fixed x each point of the finite earlier union
lies in P_i(T^k x) for only finitely many k: P_i has incoming
degree at most L and T is aperiodic. Thus the indicator of overlap
tends to zero as k tends to infinity. Dominated convergence
allows each new overlap loss to be as small as prescribed.
For U_x=union_i P_i(T^(k_i)x), it follows that

    |U_x|<=N,       incoming_degree_U<=sum_i b_i,
    b_K(U)<=sum_i q_i,
    D_0:=N-m(U)<=sum_i(n-t_i)+eta.                        (7)

The boundary inequality is subadditivity under finite unions.

At each target with incoming degree greater than N, delete the
excess pairs using a Borel order of its finite incoming fiber.
The total measure ell deleted is at most integral (sum_i b_i-N)_+.
Both degrees are now at most N. Section 2 permits deletion of
a further r<eta in pair measure and decomposition into N partial
pmp bijections. Complete them to N disjoint full-group maps.
The added pair measure is D_0+ell+r.

Let A denote this actual symmetric-vertex family. Adding or
removing one vertex changes a set's boundary by at most d. Hence

    b_K(A)<=sum_i q_i+d(D_0+2ell+2r).                     (8)

Completion pairs are pairs (root, chosen vertex) in R_X, not
new edges of K. Their K-distances can be large: (8) pays for
altered vertices and their at most d incident boundary edges,
not for paths from the root.

Combine (6)--(8) to obtain

    b_K(A)/N <= B/n + d epsilon + 2dL/(n sqrt(m))
                       +(3d+1)eta/(mn).                 (9)

Choose epsilon and its finite D, then m large, and the repair
tolerance eta. Base tests thus approximate the source ratio from
above, proving h_K(R_X)<=h_(K^pi)(R_Y).

Conversely every full-group map on X lifts using its unique
measurable group displacement. Its lift is pmp and invertible;
disjoint families and their boundary integrals are preserved.
This proves the opposite inequality and completes (2).

## 6. The remaining cost comparison

The Pichot--Vassout identity and (2) give

    inf_(K on X) h_(K^pi)(R_Y) = 2(C(R_X)-1).             (10)

Here K runs over generating bounded-degree graphings. These
suffice: include an aperiodic full-group map in a near-optimal
graphing, truncate the remaining maps, and repair the finitely
many demands of a fixed finite generating graphing on the failed
domains. This keeps the aperiodic map, gives bounded degree,
and approaches the same cost. Its consecutive powers give the
tests used for the Pichot--Vassout upper bound. The reverse bound
holds for each K. Finite-cost ergodic relations admit finite
generating graphings, as recalled in LPV Section 4.1.

If the source is also ergodic, the infimum over all its generating
bounded-degree graphings Psi is 2(C(R_Y)-1). It is at most (10).
Thus this yields the known direction C(R_Y)<=C(R_X). The gap
between the restricted and unrestricted source infima is exactly

    2(C(R_X)-C(R_Y)).                                    (11)

Equality for each pulled-back K does not permit replacing the
class of all source graphings by the class of pulled-back ones.
Showing that this replacement does not change the infimum remains
unproved. No assertion here removes that graphing-descent step.

The construction works because a projected test is a finite set
in a specified base graph, with a boundary defined independently
of the hidden source point. If Psi itself depends on that point,
the geometry changes within a fiber. The same sampling argument
then has no base boundary objective to preserve. This distinction
prevents (2) from being a proof of universal Fixed Price.
