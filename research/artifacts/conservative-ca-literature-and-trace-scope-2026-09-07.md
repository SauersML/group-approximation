# Conservative cellular automata: literature and trace scope

Focused primary-source audit, 2026-09-07. This is a literature and
hypothesis check, not a proof of the candidate theorem or a novelty
certificate. No computing jobs were used.

## Question checked and outcome

The initial question was whether an injective binary cellular automaton
over an arbitrary group, fixing zero and preserving particle count on
finite configurations, must be surjective. During the audit the working
claim was strengthened to a finite alphabet with a unique zero-charge
state and positive real charges on the other symbols, finite-configuration
injectivity, and nonincrease of total charge on finite configurations.
The proposed conclusion is conservation of charge and surjectivity.

Focused searches combining conservation, nonincrease, finite
configurations, particles, injectivity, groups, and surjunctivity did
not locate that arbitrary-group statement, nor a counterexample to it.
This bounded negative search does not establish the statement's
novelty or truth. The closest inspected sources concern conservation
laws, one-dimensional particle representations, or operator-algebra
finiteness under additional hypotheses.

## Conservation and particle representations

Marcus Pivato, *Conservation Laws in Cellular Automata*, Nonlinearity
15 (2002), [arXiv:math/0111014v2](https://arxiv.org/pdf/math/0111014).
The opening definitions use finite-support configurations and an
additive charge; footnote 1 explains the extension of the general
results from abelian to nonabelian groups. Section 6 distinguishes
conservation from the existence of a compatible local particle
displacement rule. Proposition 11 supplies that rule for the group Z;
the preceding discussion says that constructing one for arbitrary
groups is difficult. The inspected PDF has no occurrences of
"inject" or "surject". This source supports the conservation-law
framework, but does not supply an arbitrary-group particle-labeling
theorem or the surjectivity conclusion under investigation.

Andres Moreira, Nino Boccara, and Eric Goles, *On Conservative and
Monotone One-dimensional Cellular Automata and Their Particle
Representation*, [arXiv:nlin/0306040](https://arxiv.org/pdf/nlin/0306040).
The introduction explicitly restricts the paper to one dimension.
It develops particle-automaton representations for conservative and
non-increasing automata and discusses anticipation and cycles. Its
scope therefore makes it relevant to nonincrease, but does not
establish the arbitrary-group implication. The searched PDF text has
no occurrences of "injective" or "surjective".

Jarkko Kari and Siamak Taati, *Statistical Mechanics of Surjective
Cellular Automata*, Journal of Statistical Physics 160 (2015),
[publisher text](https://doi.org/10.1007/s10955-015-1281-2).
Section 2.2 specifies the lattice Z^d. The paper connects conservation
laws with invariant Gibbs measures for surjective automata. Its
surjectivity premise and lattice setting must not be silently removed
when using these results to discuss an arbitrary group.

## Conservative simulation does not give the missing full-shift compiler

Andres Moreira, *Universality and Decidability of Number-Conserving
Cellular Automata*, Theoretical Computer Science 292 (2003),
[arXiv:nlin/0306032](https://arxiv.org/pdf/nlin/0306032).
Theorem 4 encodes an arbitrary one-dimensional automaton using pairs
of opposite numerical states and then shifts the alphabet to obtain
nonnegative states. Simulation means being a subautomaton of a
rescaling, as defined in Section 2. The theorem does not assert that
injectivity on the simulated sector becomes injectivity on the whole
enlarged full shift. It also does not produce a binary automaton over
an arbitrary group. Consequently this result cannot be used without
additional work to turn the proposed conservative theorem into the
unrestricted Gottschalk theorem.

## Closest operator-algebra criterion and its exact limitation

Benjamin Steinberg, *Stable finiteness of ample groupoid algebras,
traces and applications*, Journal of Combinatorial Algebra 10 (2026),
1-52, [DOI 10.4171/JCA/118](https://doi.org/10.4171/JCA/118),
[full text](https://ems.press/content/serial-article-files/52394).
Theorem 4.1 assumes a K-dense union of orbits that are closed in the
entire unit space and discrete in their induced topology, together
with stable finiteness of the relevant isotropy-group algebras.
Corollary 7.7 gives characteristic-zero stable finiteness from a
strongly faithful invariant mean. Theorem 7.8 constructs such a mean
from a countable C-dense family of finite orbits.

These are relevant precedents, but their hypotheses have not been
established for the proposed collision crossed product. In the
gain-partition spectrum, an orbit may be discrete in its own stratum
while accumulating on another stratum. Such an orbit is not closed
in the whole spectrum. Theorem 4.1 therefore cannot simply be applied
to each stratum and declared to prove the whole algebra finite.

## Explicit counterexample to finite-height induction alone

The following elementary example shows that the last distinction is
essential, even for a global group action. It is an independent
calculation rather than a claim quoted from the references.

Let X=Z union {-infinity,+infinity} be the two-end compactification of
Z. Every integer is isolated; neighborhoods of the two added points
contain the corresponding tails. Translation n->n+1 extends to a
homeomorphism T fixing both ends. This compact zero-dimensional space
has just two Cantor-Bendixson layers. Its orbits are the discrete
integer orbit and two fixed points, but the integer orbit is not closed.
The isotropy groups are trivial or Z, so their complex group algebras
are stably finite.

Let p be the indicator of {n>=0} union {+infinity}, and q=1-p the
indicator of {n<0} union {-infinity}. Both are clopen. In the algebraic
crossed product C_lc(X,C) crossed with Z, write u for translation,
using u f u^(-1)=f composed with T^(-1). Set

    v=up+q,       v*=pu^(-1)+q.

The source pieces p and q partition X. Their images under the two
branches, T on p and the identity on q, are disjoint and cover exactly
X minus {0}. Thus direct multiplication gives

    v*v=1,       vv*=1-e_0,

where e_0 is the nonzero indicator of {0}. In particular the crossed
product is not directly finite. The represented piecewise map is
injective and omits 0, despite the finite-height orbit stratification.

This example does not contradict the collision-specific claim: its
coefficient algebra contains a half-line predicate. It proves that
finite partition height, discrete strata, and stably finite
isotropy-group algebras alone are insufficient. A valid proof for the collision
algebra must use its particular definable sets, partition structure,
or an independently justified trace or valuation.

## Partition combinatorics: useful analogies, not an identified theorem

T. A. Dowling, *A class of geometric lattices based on finite groups*,
[publisher record](https://doi.org/10.1016/S0095-8956(73)80007-3), and
Stuart Margolis, John Rhodes, and Pedro Silva, *On the Dowling and
Rhodes lattices and wreath products*,
[arXiv:1710.05314](https://arxiv.org/abs/1710.05314), provide primary
references for group-labeled partitions and their lattice structure.
These are natural combinatorial comparisons for systems of collision
equalities. Their inspected statements do not identify the proposed
arbitrary-group collision crossed product or prove its trace faithful.

The key outstanding literature comparison is therefore precise:
identify the actual coefficient algebra and its group action, then
compare its trace and finiteness argument with groupoid and
group-labeled partition results. Similar terminology alone does not
supply an existing theorem, and failure to locate an identical
statement does not establish novelty.
