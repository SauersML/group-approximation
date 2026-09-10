---
rg: 2
id: fpbs-fixed-price-universal
kind: claim
title: All free probability-preserving actions of each countably infinite group have equal cost
root: true
goal: true
artifacts:
  - research/artifacts/fpbs/docs/cost-rank-duality.md
  - research/artifacts/fpbs/docs/relative-cycle-exchange.md
  - research/artifacts/fpbs/docs/priority-assessment-2026-09-09.md
  - research/artifacts/fpbs/fixed-price-percolation.md
  - research/artifacts/fpbs/docs/fixed-price-reuse-localization.md
  - research/artifacts/fpbs/docs/fixed-price-conditional-traffic.md
---

**UNIVERSAL GOAL; OPEN.** For every countably infinite group `Gamma`, any two
essentially free probability-measure-preserving actions of `Gamma` on standard
probability spaces have the same cost.

**Scope audit, September 10, 2026.** The current proof search targets this
universal statement. The earlier September 9 priority assessment is historical.
The live reuse route still needs both
`fpbs-correlated-reuse-flags-removable` and
`fpbs-fixed-price-countable-from-finitely-generated`. The MSI validation report
`research/artifacts/fpbs/exploration-information-validation.json` now records
the computed Fixed Price frontier and the reuse premise's dependency path,
in addition to checking that this goal remains open. These are graph checks,
not mathematical proof verification.

The traffic variational identities have now been extended to every
countable group when the base action has finite cost
(`fixed-price-conditional-traffic.md`, Section 9). The repair budget
includes the complete tail of a fixed finite-cost base graphing.
Thus finite generation is not essential for that characterization.
Producing vanishing defect remains open, as does exclusion of a
finite-cost free extension over an infinite-cost free base. The
extension does not establish the finitely-generated-to-countable
passage required by the current root route.

Uniform finite fibers now exclude one part of the mixed-cost issue:
`fpbs-finite-fiber-cost-bound` proves C(X)-1<=q(C(Y)-1) for a
uniform q-point free factor. It also identifies exact preservation
for all such factors with the finite-index multiplicativity question
for specified actions; that equality has not been proved here.
The increasing-factor limit step is valid over a finite-cost base,
but cannot supply cost preservation at its finite stages.

The same bound applied to the invariant set of largest conditional
atoms excludes finite-cost sources over ergodic infinite-cost bases
whenever the conditional measures have an atomic part. A mixed-cost
factor with an ergodic infinite-cost base would therefore need
nonatomic conditional measures. That remaining case is not excluded.

Rechecked [Abert--Weiss, Corollary 2](https://arxiv.org/pdf/1103.1063) and
[Tucker-Drob, Corollary 6.22](https://arxiv.org/pdf/1211.6395): the former
has the stated finite-generation hypothesis; the latter extends cost
monotonicity under weak containment in specified cases, including when the
weakly containing action has finite cost. Neither statement supplies the
reverse comparison between arbitrary free actions. The
[higher-rank theorem](https://annals.math.princeton.edu/articles/22425)
settles its stated class of lattices, not this universal claim.
The July 2026 [product-neighbourhood preprint, Introduction and Theorem 1.1](https://arxiv.org/html/2607.20273v1)
also explicitly lists the universal problem as open and gives a sufficient
finite-set criterion for fixed price one; that criterion is not asserted for
every group.

The reverse Bernoulli comparison now has a second conditional route,
`fpbs-bernoulli-lower-bound-from-cycle-tails`. Its additional open premise
is `fpbs-bernoulli-cycle-tail-compactness`. This would establish the stronger
Bernoulli cost--Betti equality and then use the homological lower bound for
all other free actions. The coherent sparse-column calculation in
`research/artifacts/fpbs/docs/cost-cycle-structure.md`, Section 8, verifies
the reduced-circulation estimate for F_r x Z only. The universal compactness
assertion and the countable-group passage remain open.

A third conditional route now uses
`fpbs-relative-cycle-block-localization`. The proved connected-rounding
bound is C(X)<=c(Phi)+(1+2d M^2)Tr(P_out K), where K is the relative
cycle operator and P_out records edges crossing finite connected
blocks. This controls the actual cost of a generating base graphing.
Finding near-optimal source graphings and blocks making that error
vanish remains OPEN. The new route compares relative surplus and
does not require cost--Betti equality. Its computed dependency path
is included in the MSI validation report.

The cost of an action is the infimum of the costs of the graphings that
generate its orbit equivalence relation, a graphing's cost being half the
expected degree of its graph; see Gaboriau, *What is... cost?*,
arXiv:1011.2294, for the definitions and for the value `1` as a lower bound
for every aperiodic relation. A group all of whose free actions share one cost
is said to have **fixed price**. *Fixed price one* is the strictly stronger
statement that the shared value is `1`. The two must never be interchanged;
the distinction is load-bearing in every item below.

**What is known unconditionally.**

* *Bernoulli maximality.* For finitely generated `Gamma`, Abert--Weiss,
  arXiv:1103.1063, Corollary 2, prove that Bernoulli actions are weakly
  contained in every free action and therefore have maximal cost,
  `C(alpha) <= C(b_Gamma)` for every free `alpha`. This is
  `fpbs-bernoulli-maximal-cost`, imported by the citation route
  `fpbs-bernoulli-maximal-cost-reference`. It supplies one of the two
  inequalities. Proving `C(alpha) >= C(b_Gamma)` for every free `alpha` is
  the entire remaining content of the goal in the finitely generated case.
* *Property (T) gives cost one, not fixed price one.* Hutchcroft--Pete,
  *Kazhdan groups have cost 1*, arXiv:1810.11015, prove that every countably
  infinite group with property (T) has cost `1`; their abstract adds "It
  remains open if they have fixed price 1". Recorded as
  `fpbs-kazhdan-groups-have-cost-one`. The distance between an infimum over
  actions and a common value is precisely what this goal must close.
* *Amenable groups.* Every amenable group has fixed price, with cost `1`
  (Lyons, arXiv:1109.5418, Section 1, attributing this to Gaboriau 2000).
* *Cost and the first L2-Betti number.* `beta_1^(2)(Gamma) <= C(alpha)-1`
  for every free action of an infinite group, recorded as
  `fpbs-amen2-betti-cost-input`. It bounds cost from below; it never supplies
  action-independence.
* *The one proved bridge to percolation.* Lyons, arXiv:1109.5418, Section 1:
  if `Gamma` does not have fixed price with cost one, then every one of its
  Cayley graphs has a parameter at which infinitely many infinite clusters
  appear almost surely. Recorded as
  `fpbs-non-fixed-price-one-has-nonuniqueness`; it is the only established
  implication in this graph running from cost to
  `fpbs-benjamini-schramm-universal`.

**Decomposition supplied by the 2026-09-08/09 archive.** One live route
targets this claim: `fpbs-fixed-price-from-bernoulli-cost-equality` sandwiches
every free action of a finitely generated group between the Abert--Weiss upper
bound `fpbs-bernoulli-maximal-cost` and the missing reverse inequality
`fpbs-free-action-cost-at-least-bernoulli-cost`, then transfers to countable
groups through `fpbs-fixed-price-countable-from-finitely-generated`. Only the
upper bound is in hand. Four further routes are recorded and dead, each killed
by an established obstruction: `fpbs-dead-copy-source-correlations`
(`fpbs-source-statistics-not-reproducible-in-bernoulli`),
`fpbs-dead-fusf-connected-betti-descent`
(`fpbs-fusf-not-connected-on-some-cayley-graphs`),
`fpbs-dead-limit-graphing-connectivity`
(`fpbs-cost-one-routes-cannot-be-uniformly-tight` and
`fpbs-reciprocal-shortest-route-obstruction`), and
`fpbs-fixed-price-via-priority-deletion-optimality`
(`fpbs-priority-deletion-density-above-action-cost`).

The rest of what the archive supplies is class-level theorems and constructive
targets, all of which leave the universal quantifier untouched:

* fixed price one for whole classes -- `fpbs-amen2-fixed-price-one` (all
  two-generated subgroups amenable), `fpbs-bounded-exponent-two-groups-fixed-price`
  (bounded-exponent 2-groups, via Held's infinite-abelian-subgroup theorem),
  `fpbs-sc-fixed-price-family` and `fpbs-tfl-fixed-price` (explicit
  small-cancellation and torsion-free families), `fpbs-priority-composite-fixed-price`
  (composite-order profiles with divergent detour sums);
* every-action upper bounds that do not reach one -- `fpbs-qb-action-bound`
  (`C <= U_n` for `B(2,n)`, with `U_n -> 2`), `fpbs-prime-divisor-upper-cost`,
  `fpbs-burnside-common-upper-cost` (a single supremal cost `c_n` shared by
  every infinite subgroup of the large odd Burnside family);
* counterexample reductions -- `fpbs-two-generator-action-cost-witness` and
  `fpbs-positive-cost-two-generated-nonamenable` localize any cost gap to a
  two-generated nonamenable subgroup; `fpbs-burnside-explicit-action-pair`
  exhibits two free ergodic actions of `B(2,n)` with costs `c_n` and
  `1+(c_n-1)/n`, which differ exactly when `c_n>1`;
* the reuse-information programme of responses 47--55, whose remaining step
  is stated below.

**Refutation doctrine.** A counterexample does not land as a route into this
goal. It lands as an ESTABLISHED negation claim,
`fpbs-fixed-price-counterexample-exists`, which is currently an OPEN claim
carrying its own `## Attempts`. Only when that claim is established does this
goal acquire `refuted_by: [fpbs-fixed-price-counterexample-exists]`. The two
concrete attacks on it are the Kazhdan positive-rank-gradient route
(`fpbs-kazhdan-rankgradient-counterexample-reduction`, itself established as a
conditional implication, feeding on the OPEN `fpbs-kazhdan-positive-rank-gradient`)
and the Burnside pair `fpbs-burnside-positive-upper-cost` together with
`fpbs-burnside-explicit-action-pair`.

**Decision note, 2026-09-09.** The user forwarded the closing priority verdict
of the session that produced this archive
(`research/artifacts/fpbs/docs/priority-assessment-2026-09-09.md`).
Benjamini--Schramm is the PRIMARY affirmative target; Fixed Price is the
class-level one, better aligned with the archive's constructions for producing
further special cases but not thereby closer to its universal solution. Two
consequences were recorded. First, by Lyons the only remaining case of the
cost route to percolation is the nonamenable fixed-price-**one** class, so a
Benjamini--Schramm counterexample would have to *satisfy* Fixed Price for its
group. Second, proving fixed price one for one more nonamenable group does not
advance Benjamini--Schramm at all: it moves the group into the class where the
cost obstruction supplies no threshold separation. Work on this goal should
therefore be spent on comparisons between different actions of one group, not
on new cost-one families.

**Cross-links outside the fpbs region.** The cost/L2-Betti inequality
`fpbs-amen2-betti-cost-input` is the same Gaboriau input used by the
repository's treeability obstructions: `sl2-homogeneous-action-is-not-treeable`
excludes treeings of an S-arithmetic orbit relation from `beta_2^(2)>0`, and
`non-ce-relation-is-not-treeable` excludes them from failure of Connes
embeddability. Those are obstructions to treeability of a fixed relation, not
statements about equality of costs across actions, so they bound this goal's
vocabulary rather than its content.

## Attempts

* **Descend along a factor map (the archive's main line, responses 48--55,
  `docs/fixed-price-reuse-localization.md` and `docs/fixed-price-conditional-traffic.md`).**
  For an equivariant factor `pi: Y -> X` of free actions, lifting a base
  graphing gives `C_Y <= C_X` immediately; the goal needs descent. The
  reuse-localization theorem (Section 1 of the first note) proves that for
  every `epsilon>0` the extra information can be compressed to an intermediate
  factor generated by finitely many *binary* reuse decisions -- whether a
  given added edge is used more than once -- at a cost penalty below `epsilon`,
  and Corollary D makes the reuse signal rare when `C_Y=1`. **Where it dies:**
  Section 7 of that note states the missing statement exactly. One must choose
  source-near-optimal routing plans with vanishing *conditional* traffic
  penalty for the projection `a x b -> b`, equivalently prove cost preservation
  for all free binary symbolic extensions. Nonnegativity of the Jensen gaps, a
  finite alphabet, martingale convergence for a fixed plan, and smallness of
  the reuse signal's measure each fail to give that simultaneous optimization.
  The note's own warning (14) shows only that a hypothetical gap forces
  unbounded traffic multiplicities, not that the gap is absent.
* **Remove the correlated information by replacing it with independent
  randomness.** Bernoulli information can be discarded without changing cost
  (Theorem C of the same note gives `C(a x b) = C(a) <= C(b)`). **Where it
  dies:** applying that theorem to the other projection `a x b -> b` would
  confuse independence of the two probability-space coordinates with
  independence of the orbit labels in `a`, which is unavailable for arbitrary
  `a`. An edge may serve many requests while being paid for once, and a
  low-cost graphing can use long-range correlations to decide which edges are
  shared; the priority assessment, Section 4, states this as the structural
  reason the reverse Abert--Weiss inequality resists estimate-shrinking.
* **Identify action cost with a canonical spanning-forest algorithm.**
  Response 47 tested the natural universal extension of the finite-priority
  deletion construction: give every edge an independent priority, inspect all
  sufficiently short cycles, and delete an edge whose cycle-mates all have
  lower priority. It is defined on every Cayley graph and keeps the finite
  induction that guarantees connectivity. **Dead as an optimality claim:**
  response 47 exhibits a group already known to have fixed price one on which
  this algorithm's edge density does not approach the minimum graphing cost.
  No canonical local deletion rule can therefore compute action cost.
* **Prove fixed price one for one more class and iterate.** The archive's
  class results above are genuine, and the explicit Burnside bound of
  response 34 (`docs/fixed-price-burnside-explicit-bound.md`) is quantitative.
  **Where it dies:** Section 6 of that note proves `n(2-U_n)/log n -> 1`, so
  the explicit bound tends to two, not one, and Section 7 shows the
  construction does not self-improve: reapplying it to the thinned graphing
  returns the same bound rather than multiplying the excess by a factor below
  one. Section 5 of the priority assessment adds the strategic version -- the
  universal obstacle is a comparison, so another cost-one family does not
  approach it.
* **Refuting the conjecture** is represented by
  `fpbs-fixed-price-counterexample-exists`, not by a route into this goal.
