# Retained-boundary block rounding has an isoperimetric cost floor

September 17, 2026. Written deductions over the established rounding
bound `fpbs-relative-cycle-block-rounding-bound` (Theorem 6.1 of
`relative-cycle-exchange.md`) and Mader's edge-connectivity theorem for
vertex-transitive graphs. Fixed price is not resolved. No priority is
claimed.

## 0. What is killed, and why it is not the wave-4 obstruction

Theorem 6.1 rounds a generating graphing H by one fixed rule: inside
every finite block choose a spanning tree and **retain every crossing
edge**. Its premise (14), the open node
`fpbs-relative-cycle-block-localization`, is a weighted boundary estimate
on the relative operator K.

The wave-4 node `fpbs-oblivious-certificates-never-localize` kills the
premise for base-oblivious certificates. It charges the diffuse cycle
weight D(Phi) against the factor (1+2dM^2), and it needs constant label
occupancy.

Here the invariant is different. It is the **excess boundary density**
of the conditional support H at the block partition,

    eps_bd(H,E) = integral sum over components C of H|_B(x)
                  of (|boundary_H C|/2 - 1) / |B(x)|  dmu(x).

The step that dies is the rule itself. Its output always costs exactly
1 + eps_bd(H,E), whatever K is and whatever premise is used to bound it
(Lemma 2). If the conditional support contains a fully supported
generating Cayley graphing of a nonamenable group, this cost is at least
1 + (1/2 - 1/d_0) h(Gamma,S_0) for every partition (Theorem 4). The kill
uses no occupancy values, no cycle weights, no block-size factor, and no
obliviousness. It covers every certificate whose conditional support
contains a fully supported nonamenable generating label set, including
correlated and base-dependent ones.

The obstruction does not cover the retraction residual of Section 7 of
the exchange artifact, or any other rounding that deletes crossing
edges. Section 8 below explains why it cannot: after contraction,
bridge thinning is a cost problem for the contracted relation.

## 1. Setting

Gamma is an infinite finitely generated group acting freely by p.m.p.
maps on (X,mu). A finite-label graphing H has a finite label set S,
one representative from each pair {s,s^{-1}}. Its edges are pairs
{x,s.x} with s in S. Freeness identifies each orbit with Gamma and each
orbit graph of H with a spanning subgraph of Cay(Gamma,S). The cost is
c(H) = (1/2) integral deg_H dmu.

A finite-block partition E is a measurable equivalence subrelation with
finite classes. The classes are the blocks, and B(x) is the block of x.
An H-edge **crosses** when its endpoints lie in different blocks. For a
finite vertex set C in an orbit, boundary_H C is the set of H-edges with
exactly one endpoint in C.

**Mass transport on blocks.** For a nonnegative Borel function F of a
finite marked set, invariance of mu gives

    integral F(y) dmu(y) = integral (1/|B(x)|) sum_{y in B(x)} F(y) dmu(x).   (MT)

Send mass F(y)/|B(x)| from x to every y in B(x). The total sent from x
is the right side of (MT). The total received at y is F(y), because y
receives F(y)/|B(y)| from each of the |B(y)| points of its block. The mass transport
principle for countable p.m.p. relations equates the two integrals.

**The retained-boundary rounding.** Let H'(H,E) consist of all crossing
H-edges, together with a spanning tree of each connected component of H
restricted to each block. Blocks are finite, so a Borel choice exists
(for instance the lexicographically least spanning tree for a Borel
linear order of X). Theorem 6.1 uses exactly this H' when the blocks are
H-connected.

## 2. Lemma 1: the rounding generates

H'(H,E) is a subgraphing of H generating the same relation as H.

*Proof.* A crossing H-edge is retained. An internal H-edge {x,y} joins
two points of one component C of H restricted to B(x), and the retained
spanning tree of C contains a path from x to y. QED.

## 3. Lemma 2: exact cost of the rounding

For every finite-label H and every finite-block partition E,

    c(H'(H,E)) = 1 + eps_bd(H,E).                               (EX)

*Proof.* Apply (MT) to F = deg_{H'}/2. For a block B,
sum_{y in B} deg_{H'}(y) = 2 (internal retained edges) + (crossing
edges at B). The internal retained edges number sum_C (|C|-1) over the
components C of H|_B. A crossing edge at B has one endpoint in B, and
that endpoint lies in exactly one component C. Every H-edge leaving a
component C of H|_B leaves B, for otherwise C would not be a component.
So the crossing edges at B are the disjoint union of the sets
boundary_H C. Hence

    (1/|B|) sum_{y in B} deg_{H'}(y)/2
       = (1/|B|) sum_C (|C| - 1 + |boundary_H C|/2)
       = 1 + (1/|B|) sum_C (|boundary_H C|/2 - 1),

and integrating gives (EX). QED.

With singleton blocks, (EX) reads c(H) = 1 + integral (deg/2 - 1), as it
should. The identity says the rounding rule leaves **nothing for K to
control**. Its output cost is a combinatorial functional of H and E, and
a premise such as (14) can only certify an upper bound on this number.

## 4. Lemma 3: an M-free bound for the same rounding

Let pi:(Y,nu)->(X,mu) be a free factor and Phi a finite-label generating
graphing on Y. Disintegrate nu = integral nu_x dmu(x) equivariantly. For
a base edge e at x let p_e(x) be the nu_x-probability that the lifted
edge lies in Phi. For e={x,s.x} this is p_s(x). For e={s^{-1}.x,x} it
is p_s(s^{-1}.x), because nu_{g.x} = g_* nu_x. Let H keep the base edges
with p_e>0. The set of y carrying a Phi-edge whose base edge has p_e=0
is null: its measure is at most a countable sum of integrals of p_s over
{p_s=0}. So for nu-a.e. y, Phi_y is a subgraph of H on the orbit.

Lift E to Y along the orbit identification. For every finite-block
partition E, H-connected or not,

    c(H'(H,E)) <= c(Phi) + A(Phi,E) + kappa(Phi,E),              (M0)

    A     = (1/2) integral sum_{e at x, e crosses} (1 - p_e(x)) dmu(x),
    kappa = integral (comp(Phi_y|_B(y)) - comp(H|_B(pi y))) / |B(y)| dnu(y).

Both terms are nonnegative: A because p_e<=1, and kappa because
Phi_y|_B is a spanning subgraph of H|_B.

*Proof.* By (MT) on Y, c(Phi) is the integral of (1/|B|) times the
number of internal Phi-edges in B plus half the crossing Phi-edges at B.
A graph on |B| vertices with comp(Phi_y|_B) components has at least
|B| - comp(Phi_y|_B) edges. Undo (MT) for the crossing part and
disintegrate over x. This gives

    c(Phi) >= (1/2) integral sum_{e at x, crosses} p_e(x) dmu(x)
              + integral (|B| - comp(Phi_y|_B))/|B| dnu(y).

Lemma 2's computation gives

    c(H') = (1/2) integral sum_{e at x, crosses} 1 dmu(x)
            + integral (|B| - comp(H|_B))/|B| dmu(x).

The block and its component count are base-measurable, so the second
integral may be taken over nu. Subtract. QED.

Compared with (10), (M0) has no factor 2dM^2 and no cycle weights, and
it does not need H-connected blocks. So it escapes the wave-4 kill on
amenable groups. On Z^2 take p_{s_0}=1 and p_t=eps. Use blocks that are
L x L squares off a set of measure delta, with singletons elsewhere, as
Rokhlin's lemma for Z^2 provides. On the squares the crossing t-edges
contribute (1-eps)/L to A, and kappa gets at most 1/L because each row
is a Phi-path. Singletons add at most 2 delta to A. So A + kappa -> 0. But this only re-proves cost one for amenable actions by
tilings. Theorem 4 shows (M0) can do no more for fully supported
certificates.

## 5. Theorem 4: the isoperimetric floor

Let S_0 be a finite generating set of Gamma, one representative from
each inverse pair, and let d_0 be the degree of Cay(Gamma,S_0). Let

    h(Gamma,S_0) = inf over finite nonempty F of |boundary F| / |F|

in Cay(Gamma,S_0). Suppose H is a finite-label graphing containing every
edge {x,s.x} with s in S_0, for mu-a.e. x. Then for every finite-block
partition E,

    c(H'(H,E)) >= 1 + (1/2 - 1/d_0) h(Gamma,S_0).                 (FL)

*Proof.* Fix a block B and a component C of H|_B. Every edge of
Cay(Gamma,S_0) with exactly one endpoint in C is an H-edge leaving C, so
|boundary_H C| >= |boundary_{S_0} C|. Two bounds hold:

1. |boundary_{S_0} C| >= h(Gamma,S_0) |C|, by definition of h.
2. |boundary_{S_0} C| >= d_0. This is Mader's edge-connectivity theorem
   for vertex-transitive graphs, in the form for finite sides. The proof
   is included because the graph is infinite.

If d_0 >= 2, bound 2 gives 1 <= |boundary C|/d_0, so

    |boundary_H C|/2 - 1 >= (1/2 - 1/d_0) |boundary_H C|
                         >= (1/2 - 1/d_0) h(Gamma,S_0) |C|.

Sum over the components of H|_B, divide by |B| and integrate. Lemma 2
gives (FL). If d_0 = 1, Gamma is finite, which is excluded. QED.

**Proof of bound 2.** The representatives make Cay(Gamma,S_0) a simple
connected infinite d_0-regular graph on which Gamma acts
vertex-transitively. Let lambda be the least value of |boundary F| over
finite nonempty F. Call a minimizer of least cardinality an *atom*.

- *Two distinct atoms A, A' are disjoint.* Otherwise A meet A' is a
  nonempty proper subset of A, since |A| = |A'|. The union is finite, so
  its complement is nonempty. The edge boundary is submodular:
  |boundary(A meet A')| + |boundary(A join A')| <= |boundary A| +
  |boundary A'| = 2 lambda. Both terms are at least lambda, so
  |boundary(A meet A')| = lambda, contradicting the minimality of |A|.
- *The induced graph on an atom A is regular.* If x,y lie in A, choose
  g in Gamma with g.x = y. Then g.A is an atom containing y, so g.A = A,
  and g restricts to an automorphism of the induced graph. Let k be its
  degree. Then d_0 - k >= 1, because A is finite and the graph is
  connected and infinite.

So lambda = |A| (d_0 - k) >= |A|. Each vertex of A also has at most
|A| - 1 neighbours inside A, so lambda >= |A| (d_0 - |A| + 1). The
function n(d_0 - n + 1) is concave with value d_0 at n = 1 and n = d_0.
So lambda >= d_0 when |A| <= d_0, and lambda >= |A| >= d_0 + 1 otherwise.
QED.

For torsion-free Gamma not cyclic, |S_0| >= 2, d_0 = 2|S_0| >= 4, and the
floor is at least 1 + h(Gamma,S_0)/4. Bound 1 uses boundary edges, not
boundary vertices. The floor is positive exactly when Gamma is
nonamenable (Følner's criterion).

**Monotonicity.** Enlarging S_0 can only enlarge boundaries. So one fixed
fully supported generating S_0 gives (FL) for all later label sets
containing it. The degree bound d_n of (14) plays no role in (FL).

## 6. Corollary 5: the kill

Let pi:Y->X be a free factor and Phi a finite-label generating source
graphing whose occupancy is fully supported on some generating S_0:
p_s(x) > 0 for mu-a.e. x and every s in S_0. Put
F_0 = 1 + (1/2 - 1/d_0) h(Gamma,S_0). Then:

(a) For every partition into H-connected blocks of size at most M, and
every d >= deg H,

    (1 + 2 d M^2) Tr(P_out K) >= F_0 - c(Phi).

(b) For every finite-block partition, A(Phi,E) + kappa(Phi,E) >= F_0 - c(Phi).

(c) Every rounding bound whose output is the retained-boundary graphing
H'(H,E) proves at best C(X) <= F_0 from Phi.

*Proof.* Invariance of mu gives p_s(g.x) > 0 a.e. for every g. So H
contains every S_0-edge on a.e. orbit, and Theorem 4 applies. For (a),
Theorem 6.1 constructs exactly H'(H,E), and its (10) states
c(H') <= c(Phi) + (1+2dM^2) Tr(P_out K). Combine with (FL). For (b),
combine (M0) with (FL). Part (c) is (FL) itself. QED.

So along any sequence of near-optimal certificates Phi_n with
c(Phi_n) -> C(Y), if infinitely many are fully supported on a fixed
generating S_0 and C(Y) < F_0(S_0), then (14) fails along that
subsequence by at least F_0 - C(Y) - o(1). This holds for every choice of
blocks, block sizes and degree bounds.

## 7. Calibration: the class dies where the conclusion is true

Take Gamma = F_2 x Z and S_0 = {a,b,t}. The degree is d_0 = 6. For a
finite F, count only horizontal boundary edges in each layer
F_k = F meet (F_2 x {k}). A finite subset U of the 4-regular tree has
at most |U|-1 internal edges, so |boundary U| >= 4|U| - 2(|U|-1) >=
2|U|. Hence h(Gamma,S_0) >= 2 and

    F_0 >= 1 + (1/2 - 1/6) * 2 = 5/3.

F_2 x Z has fixed price 1, since it has an infinite normal amenable
subgroup, the centre (see the table in
`benjamini-schramm-frontier-map.md`). Let a, b be any free actions and
Y = a x b -> X = b. Every source certificate of cost below 5/3 with each
of a, b, t fully supported violates (14) by at least 5/3 - c(Phi). For
near-optimal certificates the violation is 2/3 - o(1). The same holds for
(M0). The occupancy may depend on the base in any way, provided it never
vanishes on a set of positive measure. The lifted base graphing of cost
1+eps has K = 0 and localizes with singleton blocks. It escapes only
because its conditional support is not fully supported on {a,b,t}.

Gamma = F_r x Z gives d_0 = 2r+2, h >= 2r-2 and
F_0 >= 1 + (r-1)(r)/(r+1). So the floor grows linearly in r while the
cost stays 1.

On Z^2 there is no floor (h = 0), in agreement with Lemma 3's Følner
computation. So this obstruction and wave-4's are complementary on
their common ground. Wave-4 needs beta_1 = 0, torsion-freeness and
obliviousness, and it also works on amenable groups. This one needs
nonamenability and full support, and it works for every occupancy
function.

## 8. What the obstruction says about the route

*The operator K is idle for this rounding.* By (EX), (10) gives
C(X) <= 1 + eps_bd(H,E) <= c(Phi) + (1+2dM^2) b(K,E). So (14) implies
the K-free statement

    (BF)  inf over E of c(H'(H_n,E)) <= c(Phi_n) + o(1),

and (BF) already gives C(X) <= C(Y), by Lemma 1. (BF) is also equivalent
to factor-cost preservation: lift a near-optimal base graphing and use
singleton blocks. It is no easier than (14), and no harder. It shows
that the cycle operator adds nothing for this rounding rule. A proof of
(14) is at least a proof that the conditional support has small
excess boundary at some partition.

*Support thinning is forced.* Suppose Gamma is nonamenable and Phi_n are
near-optimal certificates satisfying (14). Then for every generating
S_0 with F_0(S_0) > C(Y), eventually some s in S_0 has
mu{p_s = 0} > 0. The label occupancy must vanish exactly, not
approximately, on a base-measurable set of positive measure. Wave 4
found that crossing-edge occupancy must be almost base-measurable. Here
the conditional support itself must lose enough base-determined edges
to destroy the Cheeger constant at the block scale. The quantitative
requirement is (BF).

*What survives.* Roundings that delete crossing edges are not covered:
the one-bridge-per-block-pair retraction of Section 7 of
`relative-cycle-exchange.md`, and any quotient treeing. Their output
cost is not given by (EX). But after contraction to a block transversal
it is the cost of the contracted relation, as in the Section 5 normal
form. So the missing input is again a cost statement.

## Sources and certificate boundary

- `fpbs-relative-cycle-block-rounding-bound` (established): inequality
  (10) and the construction of H' (Theorem 6.1 of
  `relative-cycle-exchange.md`). This is used only in Corollary 5(a).
- Mader's theorem on edge connectivity of vertex-transitive graphs. The
  finite-side version used here is proved in Section 5.
- Følner's criterion, h(Gamma,S_0) > 0 iff Gamma is nonamenable. This is
  used only for the remark after (FL).
- Fixed price 1 for F_2 x Z (infinite normal amenable subgroup). This is
  used only in the calibration.
- Lemmas 1-3, Theorem 4 and Corollary 5(b),(c) are proved here by mass
  transport and finite graph counting.
