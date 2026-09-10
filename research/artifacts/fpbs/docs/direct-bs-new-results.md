# Direct Benjamini--Schramm: checking the new isoperimetric inputs

September 10, 2026. The target is p_c(G)<p_u(G) for every prescribed
nonamenable locally finite Cayley graph. The deductions below check two
proposed uses of recent literature. They do not prove that target and
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

## 5. Effect on the direct proof search

The elementary proposition rules out direct use of the new weighted
profile criterion on the critical quotient at weak sprinkling. Equation
(4) identifies the information lost by replacing free connections with
wired ones. Neither assertion rules out a stronger use of cohesive cuts
that controls two infinite components while retaining the exact bond law.
No such estimate or construction is proved here, and no new OPEN premise
is introduced merely to rename the original threshold-separation problem.
