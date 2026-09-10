# Direct Benjamini--Schramm: checking isoperimetry and two-cluster inputs

September 10, 2026. The target is p_c(G)<p_u(G) for every prescribed
nonamenable locally finite Cayley graph. The deductions below check several
proposed uses of the literature. They do not prove that target and
are not claims of novelty, referee review, or formal verification.

## 1. What the September theorem supplies

Hartarsky--Severo--Teixeira, *Weighted isoperimetry implies percolation*,
[arXiv:2609.07768v1, Theorem 1.1](https://arxiv.org/pdf/2609.07768),
use edge intensities lambda_e with opening probabilities 1-exp(-lambda_e).
For an infinite weighted graph put

    psi_lambda(n)=inf{weight(boundary A): n<=|A|<=2n},
    Sigma_lambda=sum_(k>=0) 1/psi_lambda(2^k).

Their hypothesis is Sigma_lambda<1/625. It yields a positive lower
bound on connection to infinity. The finite-graph statement bounds
two-point connectivity; the infinite-graph argument wires the exterior
to one vertex. The paper's reference to a solved Benjamini--Schramm
conjecture concerns p_c<1 under isoperimetric dimension greater than one.
It is not a resolution of the nonuniqueness conjecture studied here.

The proof also charges the internal connectivity requirements of a cut,
through its notion of cohesion. This is potentially useful when mere
cutset counting overcounts configurations, but its conclusion and
profile hypothesis must both be retained.

## 2. The critical quotient fails this test at weak sprinkling

Let G have degree d, let c=p_c(G), and let Q be its critical-cluster
multigraph from [the quotient construction](../critical-quotient-sprinkling.md).
Fix t in (0,1) and put ell=-log(1-t). Give each individual Q-edge
intensity ell. Equivalently, a bundle of b parallel edges has intensity
b ell and connection probability 1-(1-t)^b. This is the actual conditional
sprinkling law, corresponding to p=c+(1-c)t on G.

**Proposition.** Almost surely Q contains infinitely many vertices of
mass one and degree d. Consequently, for every ell>0,

    psi_ell(1)<=d ell,
    Sigma_ell>=1/(d ell).                                (1)

In particular the profile hypothesis in Section 1 cannot hold when

    0<t<=1-exp(-625/d).                                  (2)

The same obstruction survives deleting any finite set of candidates
from the profile's infimum, as in a version avoiding distinguished roots.

**Proof.** Since G is infinite and locally finite, choose infinitely many
vertices at pairwise distance at least three. Their incident edge sets
are disjoint. The events that all edges incident to each chosen vertex
are closed at c are independent and have common positive probability
(1-c)^d; here c<1 by nonamenability. Infinitely many occur almost surely.
Every such event gives a singleton critical cluster, and all its d
incident edges remain intercluster edges after contraction. Parallel
edges still count separately, so its total boundary intensity is d ell.

A singleton is admissible in psi_ell(1). The first summand in Sigma_ell
proves (1). If Sigma_ell<1/625, necessarily d ell>625, which is precisely
the negation of (2). Infinitely many singleton candidates remain after
any finite exclusion. QED.

The argument applies simultaneously to all ell>0 on the same event of
full critical-configuration probability. It does not compare thresholds
of arbitrary nontransitive graphs. It only shows that this particular
sufficient criterion is unavailable near t=0 on the actual quotient.
The quotient still has p_c(Q)=0 by the exact coupling. No contradiction
arises: a sufficient percolation criterion need not detect its onset.

Deleting all small cells or contracting further cells is a different
operation. Such a replacement would need its own proof that it preserves
the original Bernoulli law and the count of infinite components.

## 3. What wiring forgets, exactly

This next identity is deterministic. Let omega be any edge configuration
on a connected locally finite graph, let x,y be fixed vertices, and let
V_n be an increasing finite exhaustion containing them. In the wired
graph collapse every vertex outside V_n to a single vertex, preserving
all edges from V_n to its exterior. Write W_n for wired connectivity of
x and y, and I_x,I_y for infinitude of their original omega-components.
Then W_n decreases with n and

    intersection_n W_n = {x connected to y in omega}
                         union (I_x intersect I_y).       (3)

Indeed, an original open path projects to every wired graph. If both
components are infinite, each reaches the exterior of every V_n, so
they join at the wired vertex. Conversely, suppose their components
are distinct and one is finite. Once V_n contains that finite component,
it has no open edge to the exterior and cannot acquire a wired path
to the other component. This proves (3).

Under any probability law, continuity from above therefore gives

    lim_n P(W_n)=P(x connected to y)
                 +P(I_x,I_y,x not connected to y).        (4)

The second term is precisely a two-distinct-infinite-cluster event.
Thus a bound on wired connectivity does not by itself bound the free
two-point function. Removing that term requires additional information
about the very phenomenon in the target conjecture.

For calibration, take the 4-regular tree, a Cayley graph of F_2, and
any p in (1/3,1). The free two-point function is p^dist(x,y), since
there is exactly one simple path. On the other hand FKG gives
P(I_x,I_y)>=theta(p)^2>0, so (4) is at least theta(p)^2 uniformly
in x,y. When dist(x,y) is large, the excess is strictly positive.
This directly demonstrates the distinction on a graph within our target
class; it is not a counterexample to Benjamini--Schramm.

## 4. The August cluster-graphing note does not give right continuity

Chu, *Applications of the cluster graphing*,
[arXiv:2608.06644v1, Section 1.A](https://arxiv.org/html/2608.06644v1#S1.SS1),
gives equivalence-relation proofs of the known absence of critical
infinite clusters. In the monotone coupling, take p_n increasing to p_c
from below. Every path at p_c uses finitely many edges, all with labels
strictly below p_c almost surely, so

    R_(p_c)=union_n R_(p_n).

The approximating relations have finite classes, hence the union is
hyperfinite. The first proof's HTML version reads p_u in the sentence
describing this sequence; the asserted finite approximants require p_c.
We do not use that sequence with p_u in place of p_c.

This left-limit argument gives no interval of hyperfiniteness or
nonuniqueness to the right of p_c. The sparse-separator deductions in
[sparse base surgery](sparse-base-surgery.md) likewise do not supply it.

## 5. The finite-cluster restriction in the two-ghost inequality

Easo--Hutchcroft, *The critical percolation probability is local*,
[arXiv:2310.10983v1, Theorem 2.5](https://arxiv.org/pdf/2310.10983),
recall the following bound on a unimodular transitive graph of degree d.
For an edge e and n>=1, let S_(e,n) mean that its endpoints belong to
distinct clusters of size at least n, **at least one of them finite**.
The edge is necessarily closed. For p in (0,1],

    P_p(S_(e,n)) <= C_d sqrt((1-p)/(p n)).                (5)

Their Lemma 2.6 extends a related estimate to two specified vertices
under p<p_c, when all clusters are finite. Neither statement bounds the
probability that two infinite clusters are distinct in the supercritical
regime. Dropping the finite-cluster restriction from (5) is false.

Here is the precise distinction. Let A_(e,n) require distinct global
clusters of size at least n with no finiteness restriction, and let D_e
require distinct infinite clusters. Then, disjointly,

    A_(e,n) = S_(e,n) union D_e.                         (6)

Thus (5) controls the error in approximating P_p(D_e) by P_p(A_(e,n));
it supplies no positive lower bound on either quantity. A_(e,n) still
tests connectivity in the entire graph, despite its finite size cutoff.

This is also visible in an exact finite-volume limit. Fix an increasing
finite vertex exhaustion V_R containing the endpoints of e. Let A_(R,n)
mean that the endpoints lie in distinct clusters of size at least n in
the induced open graph on V_R, with free boundary. For each fixed n,

    lim_(R->infinity) 1_(A_(R,n)) = 1_(A_(e,n)).          (7)

**Proof.** If the global clusters coincide, a finite open path joins the
endpoints and lies in V_R for all sufficiently large R. If they differ,
they remain distinct in every V_R. Each cluster with at least n vertices
contains a finite connected witness of n vertices, eventually contained
in V_R; a smaller global cluster cannot acquire n vertices in V_R. These
cases prove eventual equality in (7). QED.

Bounded convergence, followed by continuity from above in n, gives

    lim_(n->infinity) lim_(R->infinity) P_p(A_(R,n))
      = P_p(D_e),
    lim_(R->infinity) lim_(n->infinity) P_p(A_(R,n)) = 0.  (8)

The second equality holds because V_R is finite. Consequently, applying
(5) to every finite induced ball with a constant depending only on the
ambient degree would wrongly force P_p(D_e)=0. Such balls need not be
transitive, and the theorem does not authorize that application.

For an explicit check, on the d-regular tree with d>=3 and
p in (1/(d-1),1), delete e and let a be the probability that its endpoint
has an infinite cluster in its remaining rooted half-tree. A branching
process gives a>0. The two half-tree configurations and the state of e
are independent, so

    P_p(D_e)=(1-p)*a^2>0.                                (9)

Thus the two limits in (8) really differ within the class in our goal.
The issue is not resolved by observing that every finite-volume cluster
is finite: the required estimate must survive the volume limit, where
two distinct infinite clusters can remain.

## 6. Small intrinsic growth does not settle uniqueness

Hutchcroft, *Slightly supercritical percolation on nonamenable graphs II*,
[arXiv:2207.00701v2, Section 2](https://arxiv.org/html/2207.00701v2#S2),
proves the universal upper bound, for p>=p_c,

    gamma_int(p) <= (p-p_c)/p_c,

where gamma_int is the exponential rate of the expected size of an
intrinsic ball, measured using open-path distance. Theorem 1.5 identifies
this with the almost-sure intrinsic growth rate on infinite clusters.
These statements do not require the L2 condition. In contrast, the
two-sided near-critical growth and quantitative anchored-isoperimetry
theorems in that paper assume p_c<p_(2->2). That assumption is an OPEN
premise in this Cairn graph and cannot be imported as a universal fact.

Uniqueness and FKG would give a positive lower bound theta(p)^2 on
P_p(o connected to x), hence exponential growth of the expected cluster
mass inside *ambient* balls. This is compatible with a small intrinsic
growth rate: a connecting open path can be much longer than the ambient
distance. No uniform comparison of those distances is supplied by the
growth theorem. The existing [query strong converse](../query-strong-converse.md)
also supplies a necessary search cost, not an upper bound on path length
or exploration cost. Therefore these inputs do not yet close that route.

## 7. Thinning gives a lower bound on connecting-path length

The subsequent attempt to control detours by thinning also did not
discharge a universal premise. Here is the exact calculation, without
an algorithmic or finite-moment assumption.

Put c=p_c(G), fix q in (c,1), and let X_n be the independent lazy-walk
endpoint from o. Write rho<1 for its operator norm. The
[critical correlation bound](../spectral-spike.md) gives
P_c(o connected to X_n)<=rho^n. Let D_q be the open-path distance
between these endpoints, with value infinity when they are disconnected.
For every nonnegative integer L,

    P_q(D_q<=L) <= rho^n (q/c)^L.                       (10)

**Proof.** Sample the q-configuration and independently retain each of
its open edges with probability c/q. The resulting edge states are
independent Bernoulli(c). On D_q<=L, choose a simple open path of length
at most L using a fixed enumeration of finite paths. Conditional on the
q-configuration and the walk, this selected path survives with probability
at least (c/q)^L. Survival implies connection in the thinned configuration.
Thus (c/q)^L P_q(D_q<=L)<=P_c(o connected to X_n)<=rho^n. QED.

For L=floor(b n) with b<(-log rho)/log(q/c), (10) decays exponentially
in n. Under uniqueness, conditioning on both endpoints being infinite
costs at most the factor theta(q)^(-2), by FKG. This excludes short
connections; it does not furnish the upper bound on path length or search
cost needed by the attempted route. The two are different tasks, since
finding a path can require queries outside that path.

The published distance-control theorem checked in this attempt is
Hutchcroft, *The L2 boundedness condition in nonamenable percolation*,
[arXiv:1904.05804v2, Theorem 3.3](https://arxiv.org/html/1904.05804#S3).
It controls intrinsic detours under p<p_(2->2). To use it at parameters
strictly above c requires the L2 threshold separation that is still OPEN
in Cairn. This is not an unconditional replacement for that premise.

## 8. Free-energy regularity does not supply the missing merger estimate

Hutchcroft, *Continuity of the Ising phase transition on nonamenable
groups*, [arXiv:2007.15625v1, Corollary 1.14](https://arxiv.org/html/2007.15625#S1.SS4),
proves that the percolation free energy

    kappa(p)=E_p[1/|C_o|], with 1/infinity=0,

is twice continuously differentiable at p_c on transitive nonamenable
graphs. Its proof uses uniform control of truncated logarithmic moments
of finite clusters. Section 1.4 also records analyticity away from p_c.

This is not, by itself, control of mergers between infinite clusters.
Deterministically, opening a single edge between two infinite components
leaves 1/|C_v| unchanged for every vertex v: it is zero on both components
before and after their merger, and all other components are unchanged.
This observation does not prove that free-energy methods can never help;
it identifies the additional connection estimate that this attempt lacks.

The finite-graph derivative identities in
[cluster-contact mergers](cluster-contact-mergers.md) concern
E_p[number of clusters]/|V|. On a nonamenable exhaustion, this average
must not be identified with kappa(p) without a separate argument. An
explicit calibration already fails on the d-regular tree, d>=3.
Every finite induced ball is a tree, so its mean cluster count per vertex
is 1-p(|V|-1)/|V|, tending to 1-p. In the infinite tree, for
0<p<1/(d-1), all clusters are finite and

    kappa(p)=1-d p/2.                                   (11)

For completeness, in a finite tree cluster C the average open degree is
2-2/|C|. Mass transport makes the expected open degree at the original
root equal to the expected cluster-average open degree: let each vertex
send its open degree divided by |C| to every vertex of C. Its expected
outgoing mass is d p, while its incoming mass is 2-2/|C_o|. Taking
expectations proves (11). The two limits differ for d>=3 and p>0.
The boundary-weighted finite-ball average therefore does not transfer
the finite merger identities to the desired rooted observable.

## 9. Nonuniqueness at the uniqueness threshold can mean no percolation

The final literature check was Hutchcroft--Pan, *Percolation at the
uniqueness threshold via subgroup relativization*,
[arXiv:2409.12283v1, Definition 1.11 and Theorems 1.13--1.15](https://arxiv.org/html/2409.12283#S1.SS2).
For a subgroup H, a cluster is H-infinite when its intersection with H
is infinite. An obstacle to uniqueness rules out exactly one H-infinite
cluster at the relative uniqueness threshold. The definition explicitly
permits either zero or infinitely many such clusters.

The paper proves this property for several classes, including groups
with suitable amenable wq-normal subgroups of exponential growth,
nonamenable products, and property (T) groups. These are hypotheses on
the group, not a classification of all nonamenable groups. Moreover,
even a universal exclusion of exactly one infinite cluster at p_u would
not alone exclude p_c=p_u: zero infinite clusters at that common value
is consistent with critical finiteness. No general positive lower bound
on percolation at p_u, or threshold separation, was extracted here.

## 10. Effect on the direct proof search

The elementary proposition rules out direct use of the new weighted
profile criterion on the critical quotient at weak sprinkling. Equation
(4) identifies the information lost by replacing free connections with
wired ones. Neither assertion rules out a stronger use of cohesive cuts
that controls two infinite components while retaining the exact bond law.
The two-ghost estimate removes finite-cluster errors but does not bound
the two-infinite-cluster term from below. Finite-volume replacements must
also control connections that first appear outside the inspected volume;
equation (8) prevents an interchange of limits from supplying that control.
No such estimate or construction is proved here, and no new OPEN premise
is introduced merely to rename the original threshold-separation problem.

The thinning, free-energy, and subgroup-threshold follow-ups were three
consecutive attempts without progress toward a complete proof. The
session's research goal was consequently marked blocked on September 10,
2026. This is a status of the attempted research, not a mathematical
refutation or a claim that further research is impossible. Cairn's
universal Benjamini--Schramm claim remains OPEN, with the same eight live
conditional routes and their unproved premises. The subsequent request
to archive everything is fulfilled by recording those attempts here and
linking them from the root claim, without adding artificial proof edges.
