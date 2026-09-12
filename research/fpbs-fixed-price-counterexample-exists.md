---
rg: 2
id: fpbs-fixed-price-counterexample-exists
kind: claim
title: Some countable group has two free probability-preserving actions of different cost
root: true
distinct_from:
  fpbs-kazhdan-positive-rank-gradient: that asks for one specific algebraic object, an infinite Kazhdan group with a positive-rank-gradient Farber chain; this is the negation of the universal goal, which such a group would establish but which other constructions could establish instead.
  fpbs-burnside-positive-upper-cost: that is the numerical statement c_n>1 for one large odd Burnside exponent; only together with fpbs-burnside-explicit-action-pair does it produce the unequal pair asserted here.
  fpbs-kazhdan-rankgradient-counterexample-reduction: that is an ESTABLISHED conditional implication, positive rank gradient in an infinite Kazhdan group would refute Fixed Price; it does not decide this claim, because its hypothesis fpbs-kazhdan-positive-rank-gradient is unconstructed.
  fpbs-kazhdan-groups-have-cost-one: that is the imported Hutchcroft-Pete theorem that every infinite property (T) group has infimal cost one, which supplies a cheap action and no second action of different cost; it is an input to one attack on this claim, not a decision of it.
artifacts:
  - research/artifacts/fpbs/creative-branches.md
  - research/artifacts/fpbs/fixed-price-percolation.md
---

**OPEN; the negation of `fpbs-fixed-price-universal`.** There exist a
countably infinite group `Gamma` and two essentially free
probability-measure-preserving actions of `Gamma` on standard probability
spaces whose costs differ.

This node exists because of the graph's refutation convention. A
counterexample is not a route into the universal goal; it is an ESTABLISHED
negation claim, and only when this claim is established does
`fpbs-fixed-price-universal` acquire
`refuted_by: [fpbs-fixed-price-counterexample-exists]`. Until then the goal
stays OPEN and this node stays OPEN, and neither one is evidence about the
other.

Establishing it requires an actual pair of actions with a proved strict
inequality between two costs, each of which is an infimum over all generating
graphings. An upper bound for one action and a *lower* bound for the other are
both needed; the archive's constructions supply upper bounds in abundance and
essentially no lower bounds above the universal value one.

Any witness is heavily constrained. By `fpbs-two-generator-action-cost-witness`
and `fpbs-positive-cost-two-generated-nonamenable`, a free action of cost above
one restricts to a two-generated subgroup of cost above one, so the search may
be confined to two-generated nonamenable groups. By Lyons, arXiv:1109.5418, a
group failing fixed price one has a nonuniqueness phase on every Cayley graph,
so a witness that also fails cost one would settle
`fpbs-benjamini-schramm-universal` for that group at the same time.

## Attempts

* **Property (T) with positive rank gradient** (response 4,
  `creative-branches.md` Section 4). Hutchcroft--Pete give every infinite
  Kazhdan group cost one (`fpbs-kazhdan-groups-have-cost-one`), and
  Abert--Nikolov give
  `Cost(profinite boundary action) = 1 + lim_n (d(Gamma_n)-1)/[Gamma:Gamma_n]`
  for a Farber chain. A residually finite infinite Kazhdan group with a Farber
  chain of positive rank gradient would therefore have two actions of
  different cost, with no attainment hypothesis needed since the infimum one
  already supplies the cheaper action. The conditional implication is written
  and established as `fpbs-kazhdan-rankgradient-counterexample-reduction`.
  **Where it dies:** `fpbs-kazhdan-positive-rank-gradient` is unconstructed.
  A candidate must simultaneously keep property (T), keep the profinite
  boundary action essentially free (for instance a normal chain with trivial
  intersection), and have `liminf_n dim_{F_l} H_1(Gamma_n;F_l)/[Gamma:Gamma_n]`
  strictly positive. Large homology at finitely many levels, a non-Farber
  chain, or a presentation-deficiency count supplies none of the three.
* **Large odd Burnside groups.** `fpbs-burnside-explicit-action-pair`
  constructs, for `Gamma=B(2,n)`, a Bernoulli action of cost `c_n` and a skew
  product over `Z/nZ` of cost `1+(c_n-1)/n`; these differ exactly when
  `c_n>1`, which is `fpbs-burnside-positive-upper-cost`. **Where it dies:** no
  lower bound above one is proved for `c_n`. The pressure runs the other way:
  Donoso-Echenique and Silva prove infimal group cost one for these groups,
  response 34 (`docs/fixed-price-burnside-explicit-bound.md`) proves the
  every-action upper bound `U_n` with `n(2-U_n)/log n -> 1`, and the
  routes `fpbs-burnside-low-cost-averaged-connector-target`,
  `fpbs-cap-construction-target` and `fpbs-cut-burnside-network-target` are all
  attempts to push `c_n` down to one rather than up.
* **Find a gap through the L2-Betti obstruction.** `fpbs-amen2-betti-cost-input`
  gives `beta_1^(2)(Gamma) <= C(alpha)-1` for every free action of an infinite
  group. **Dead as a source of inequality:** the bound is uniform in the
  action, so it moves both costs together and can never separate two actions
  of the same group.
* **Read a gap off a deletion algorithm.** Response 47 tested a universal
  priority-based edge-deletion rule and showed its density does not compute
  minimum graphing cost even on a group known to have fixed price one, so a
  disagreement between the algorithm's outputs on two actions is not evidence
  of a cost gap.
* **Separate costs by soficity of actions.** Kun--Thom give the residually
  finite Kazhdan group `EL_r(F_q[x^(+-1)]) semidirect SL_d(Z)` a free nonsofic
  action (`kun-thom-free-nonsofic-action`) next to its sofic ones (Bernoulli,
  profinite), so compression rigidity might have forced a different cost.
  **Dead:** `fpbs-elementary-matrix-semidirect-fixed-price-one` gives that group
  fixed price one by a commuting root-subgroup chain, so all its free actions,
  sofic or not, have cost one. A witness must lie outside every group reached
  from an infinite amenable subgroup by a chain of infinite commensurations, as
  the Burnside branch does.
