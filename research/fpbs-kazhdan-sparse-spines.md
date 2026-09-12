---
rg: 2
id: fpbs-kazhdan-sparse-spines
kind: claim
title: All infinite Kazhdan groups admit arbitrarily sparse FIID connected infinite vertex sets
root: true
---

OPEN restricted research target. Together with the sparse-spine lemma it would prove fixed price one for this class, not for every countable group.

## Attempts

* **Use the sparse-spine lemma.** `fpbs-sparse-spine-cost-bound` proves that
  an FIID vertex set `I` that is almost surely nonempty, infinite and
  connected in the Cayley graph, with density `theta=P(o in I)`, gives
  `C^*(Gamma) <= 1+(d/2-1)theta`: keep the ambient edges inside `I` and attach
  every outside vertex along a strictly decreasing distance to `I`, breaking
  ties with extra iid labels. So spines of arbitrarily small density would
  give fixed price one for this class. The reduction is proved; only the
  construction is missing.
* **Upgrade the Hutchcroft--Pete construction to a factor of iid.**
  `fpbs-kazhdan-groups-have-cost-one` already gives a cost-one action for
  every infinite Kazhdan group, so it is natural to try to make the witnessing
  low-cost invariant percolation admissible. **Where it dies:** Section 5 of
  `research/artifacts/fpbs/exploration.md` cites [HP, Remark 4.4] for the
  reason this fails: a low-cost invariant percolation construction can cease
  being a factor of iid before producing the positive-frequency cluster needed
  to upgrade a minimum-cost result to a maximal, that is Bernoulli, cost
  result. Admissibility rather than density is the obstruction, and it is the
  same gap that keeps the published theorem at cost one instead of fixed price
  one.
* **Colour whole infinite components.** Assigning a globally constant random
  colour to an infinite component is the obvious way to select a sparse
  connected set. **Dead:** such a rule is not a factor of iid. Section 3 of
  `research/artifacts/fpbs/creative-branches.md` proposes overlapping infinite
  cells with repeated contact opportunities instead, following the
  infinite semi-touching and horoball geometry used in recent product-group
  proofs, and does not carry it out for property (T) groups.
* **Certify connectivity without short routes.** The well-founded replacement
  lemma of Section 3.1 lets a deleted edge of level `m` be replaced by a
  finite path using retained edges and deleted edges of lower level, so
  connectivity survives arbitrarily long detours and a limit of cycle
  deletions. **Where it dies:** the lemma is purely qualitative. It supplies
  no edge-intensity bound and therefore no sparsification, which is the entire
  content of this claim.
