# Cluster contacts under the actual Bernoulli merger process

Research deduction, September 10, 2026. These are elementary written
identities and obstructions, not a solution of Benjamini--Schramm, a novelty
claim, or an independently verified proof. The coalescent viewpoint itself
is classical: see Haggstrom--Peres--Schonmann, *Percolation on Transitive
Graphs as a Coalescent Process*, 1999,
<https://doi.org/10.1007/978-1-4612-2168-5_4>.

This note tests the proposed effective-neighbor statistic against the exact
merger law. It retains parallel edges in the critical quotient described in
`../critical-quotient-sprinkling.md`. No independent branching approximation
or infinite-volume moment bound is assumed.

## 1. Exact generator

Let H be a finite loopless multigraph. Give each edge an independent
uniform label, and open edges whose labels are at most p<1. Its open
components form a partition P. For distinct blocks A,B, let b_AB count
ALL original edges between them. All such edges are currently closed.
Let P/AB denote the partition obtained by merging A and B.

Conditional on the full current configuration, remaining closed labels
are independent uniforms on (p,1). Consequently every function F of the
partition satisfies the finite-state generator identity

    L_p F(P) = (1/(1-p)) sum_{A<B} b_AB [F(P/AB)-F(P)].       (1)

Opening an edge internal to a block changes no partition observable.
The right side depends only on P, so conditioning further down to P
gives the same formula. Equivalently, in time s=-log(1-p), each individual
closed edge has rate one and the merger AB has rate b_AB.

When AB merges, its k=b_AB contacts disappear from the quotient and

    b_(A union B),C = b_AC+b_BC.                             (2)

This addition is the correlation that a fresh-neighbor approximation loses.

## 2. Creation and removal of parallel contacts

Sum over unordered block pairs and unordered triples, respectively:

    N = number of blocks,
    M = sum b_AB,
    Q = sum b_AB^2,
    R = sum b_AB^3,
    T = sum_{A<B<C} b_AB b_AC b_BC,
    S = sum binom(b_AB,2) = (Q-M)/2,
    H3 = sum b_AB binom(b_AB,2).

T counts edge choices in triangles of the QUOTIENT. Such a triangle need
not be a triangle in the original graph. Contracting open paths can turn
long original cycles into quotient triangles.

**Theorem 1.** At every finite configuration,

    (1-p)L_p N = -M,
    (1-p)L_p M = -Q,
    (1-p)L_p Q = -R+6T,
    (1-p)L_p S = -H3+3T.                                   (3)

**Proof.** A merger across k edges decreases N by one and M by k.
For Q its increment is

    -k^2 + 2 sum_{C notin {A,B}} b_AC b_BC.

Multiply by the merger rate k. The first terms sum to -R. Each unordered
triangle contributes its edge-product three times, each with coefficient
two. Subtract the M identity and divide by two to obtain the S identity.
All sums are finite. This proves (3).

Thus parallel contacts have an exact source, 3T, and an exact removal
term, H3. Neither term may be dropped in an upper bound without checking
the direction. Dynkin's identity, with s as above, gives

    E S(s) + integral_0^s E H3(u) du
       = S(0) + 3 integral_0^s E T(u) du.                   (4)

For an initially closed simple host graph, S(0)=0. For an initial
contracted configuration it can be positive. Formula (4) also holds
between deterministic times and up to bounded stopping times in a finite
host graph, with the corresponding stopped integrals.

There is no closed evolution using N,M,Q alone. At the singleton
partition, the triangular prism and K_(3,3) both have (N,M,Q,R)=(6,9,9,9).
They are connected cubic Cayley graphs. The prism has T=2 and K_(3,3)
has T=0, giving (1-p)L_p Q=3 and -9, respectively. Thus even the sign is
not determined by those four statistics. This is a finite-state
obstruction, not a counterexample to a percolation phase claim.

An additional check follows directly from differentiating finite sums.
For v=|V(H)| and kappa_H(p)=E_p N/v,

    kappa_H'(p) = -E_p M/[v(1-p)],
    kappa_H''(p) = E_p(Q-M)/[v(1-p)^2]
                  = 2 E_p S/[v(1-p)^2] >= 0.              (5)

The derivative in (5) includes the derivative of 1/(1-p).

## 3. The proposed dispersion is not monotone, even on Cayley graphs

For a distinguished current block A put

    t_A = sum_B b_AB,    u_A = sum_B b_AB^2,
    D_A = t_A^2/u_A,

with D_A=0 when t_A=0. Track the block containing a fixed original root.
There are TWO kinds of changes to D_A:

* A merges with a neighboring block B. Then
  t_new=t_A+t_B-2b_AB and
  u_new=u_A+u_B-2b_AB^2+2 sum_{C notin {A,B}} b_AC b_BC.
* Two blocks B,C other than A merge. Then t_A is unchanged, while
  u_A increases by 2b_AB b_AC. If both contact A, this strictly decreases D_A.

In particular, mergers away from the root cluster matter.

**Theorem 2.** At the all-closed configuration on an infinite simple
d-regular graph, write c_v for the number of common neighbors of o and
v, and e_o for the number of edges induced by the neighbors of o. The
initial generator of the root dispersion is

    L_0 D_o = sum_{v~o} [(2d-2)^2/(2d-2+2c_v)-d]
                  + e_o [d^2/(d+2)-d].                   (6)

Indeed, initially every cluster is a singleton. Opening ov gives total
boundary 2d-2, with c_v double contacts and all other contacts single.
Opening an edge between two neighbors of o leaves total boundary d but
changes its squared-contact sum from d to d+2. Every other single edge
opening leaves the root statistic unchanged. This proves (6) directly;
the sum of nonzero single-edge increments is finite.

For the d-regular tree, (6) equals d(d-2). On the other hand, take

    G = T_4 square K_10,

the Cartesian-product Cayley graph of F_2 x C_10, using the four free
generators/inverses and all nine nonidentity elements of C_10. It is
simple, 13-regular and nonamenable. For example, slicing a finite vertex
set by the C_10 coordinate and using T_4 expansion gives boundary at
least twice its size.

The nine clique neighbors of o have c_v=8, the four tree neighbors have
c_v=0, and e_o=36. Thus

    L_0 D_o = 9(576/40-13) + 4(576/24-13)
                             +36(169/15-13)
            = -29/5.                                     (7)

The 13-regular tree, also a nonamenable Cayley graph, instead gives 143.
Both begin with the identical rooted data |A|=1, t_A=u_A=D_A=13.
Nonamenability, degree, and these initial data do not determine the sign.

These generator values also equal the right derivatives of E_p D_o at
p=0. To justify this in infinite volume, first explore C(o), then all
open clusters meeting its external vertex boundary. These two stages
determine every contact bundle of C(o), hence D_o. Dominate the first
stage by a branching tree with offspring Binomial(d,p). Each of its
vertices supplies at most d seeds for second-stage branching trees with
the same offspring bound. Previously exposed closed edges and collisions
can only reduce this exploration. Count open discoveries with a variable
z. The first-stage progeny generating function F solves
F=u(1-p+p z F)^d near (p,u,z)=(0,1,1); composing at most d such second-stage
seed factors per first-stage vertex gives a generating function analytic
for small p and for u,z in a fixed neighborhood of one. Every term with
at least two open discoveries contains at least p^2. Differentiating in
u therefore bounds the expected total explored size on that event by
O(p^2). Since D_o<=d|C(o)|, its contribution is also O(p^2).
With zero or one discovered open edge, the
first-order terms are exactly the finite list in (6). This proves the
derivative assertion. No near-critical moment assertion follows.

The negative derivative in (7) refutes universal monotonicity of this
statistic. It does not refute a near-critical averaged inequality or the
coalescent approach itself. Both example graphs have nonuniqueness phases.

## 4. What this calculation permits, and what it does not

The defensible next observable must keep track of contact overlap or a
compensating term; dispersion alone does not have a favorable drift.
The identity (4) offers a precise place to test such compensation. A
quotient triangle is a merger opportunity that turns distinct contacts
into parallel contacts, which are subsequently removed at a faster rate.
Proving that their creation and removal have suitable near-critical
balance would require a further argument using the Bernoulli law and
geometry of the fixed Cayley graph. Equation (4) supplies no such bound.

There are two separate unresolved passages:

1. **Integrability and limits.** In the actual critical quotient the
   unimodular cluster-root law has finite mean degree but infinite second
   degree moment (`fpbs-critical-quotient-palm-moments`). The elementary
   bound u_A<=t_A^2 therefore does not give the needed finite expectation.
   This does NOT assert that E u_A is infinite. On a tree every contact
   has multiplicity one, so u_A=t_A despite the infinite second degree
   moment. Finite-volume normalized identities cannot be passed to a
   Cayley graph by assuming a negligible boundary; nonamenable graphs
   have no such finite-set exhaustion.
2. **Connection to uniqueness.** Even a finite contact moment or a bound
   on total triangle production is not yet a criterion for p_c<p_u.
   An argument must relate a controlled observable to the failure of
   uniqueness at a supercritical parameter. No such implication is
   asserted here, and the root goal remains OPEN.

The earlier critical-quotient counterexamples already rule out using
expansion, unimodularity and independent sprinkling alone. The inherited
Bernoulli environment gap is recorded in
`fpbs-critical-quotient-environment-gap`; it does not by itself control
the unbounded products in T or H3.

## 5. Reproducible algebra checks

`../scripts/replay_cluster_contact_mergers.py` checks (3) by opening
individual original edges and recomputing connected components, rather
than using the quotient update to generate both sides. It exhausts all
three-state edge assignments on five labeled vertices (absent, closed,
open), checks (5) against direct derivatives of finite Bernoulli sums,
and evaluates (6)-(7) by explicit single-edge openings on sufficient
finite neighborhoods. The bounded run is on MSI; the JSON report records
its scope and source hashes. This is a check of finite algebra and the
displayed examples, not a verification of an infinite universal theorem.
