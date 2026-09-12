---
rg: 2
id: fpbs-hyperbolic-3-manifold-groups-fixed-price-one
kind: claim
title: Fundamental groups of closed hyperbolic 3-manifolds have fixed price one
root: true
distinct_from:
  fpbs-fixed-price-universal: that is the universal goal for every countable group; this is the single class of closed hyperbolic 3-manifold groups, cocompact lattices in PSL(2,C), with its own consequence for Heegaard genus.
  fpbs-normal-subgroup-bounded-cost-fixed-price-one: that is a general statement about extensions by normal subgroups of bounded action cost; this is one class it would settle through virtual fibering, and which could be settled otherwise.
---

**OPEN.** For every closed hyperbolic 3-manifold `M`, every essentially free
p.m.p. action of `pi_1(M)` has cost one.

Infimal cost one is known for these groups: a fibered finite cover gives an
infinite normal surface subgroup of infinite index, so Gaboriau's finite-cost
normal subgroup theorem applies (Gaboriau lecture notes, Theorem 2.56,
[Gab02b, Th. 3.4]). Fixed price is the open part.

**Why it matters.** Abert--Nikolov, arXiv:math/0701361, Theorem 2, verbatim:
"Either the Rank vs Heegaard genus conjecture is false or the Fixed price
problem has a negative solution." Their abstract says the conjecture "on
hyperbolic 3-manifolds is incompatible with the 'Fixed Price problem'". This
claim is the 3-manifold case of that alternative.

## Attempts

* **Normal subgroup of bounded cost.**
  `fpbs-hyperbolic-3-manifold-fixed-price-via-normal-subgroup` derives this
  claim from `fpbs-normal-subgroup-bounded-cost-fixed-price-one`, using
  virtual fibering, the fixed price `2g-1` of surface groups, and
  finite-index transfer (`fpbs-fibered-3-manifold-cost-inputs`). **Where it
  waits:** the extension statement is open. Theorem A
  (`fpbs-quotient-split-actions-have-cost-one`) gives cost one only for
  actions with a free finite-cost factor of `Z`, and the Bernoulli shift has
  none (`fpbs-quotient-split-not-bernoulli-contained`).
* **Gaboriau's chain or commensurated criteria.** These need an infinite
  subgroup of fixed price one that some chain of infinite intersections
  carries to the whole group. **Where it dies:**
  - in a torsion-free hyperbolic group the infinite amenable subgroups are
    cyclic;
  - if `<g> ∩ gamma <g> gamma^-1` is infinite, then `gamma` lies in the maximal
    elementary subgroup of `g`, which is virtually cyclic;
  - so every chain stays inside that subgroup.
* **Khezeli's product horoballs.** `pi_1(M)` contains no direct product of two
  infinite groups, and the fibered cover's product-coordinate metric fails to
  be left-invariant because the monodromy has infinite conjugacy orbits
  (`fpbs-split-product-metric-needs-finite-conjugacy-orbits`).
* **Transport graphing using every return time.** Use `t` together with the
  fibre generators restricted to a small set `A`, applied at every return of
  the `t`-orbit to `A`, not only the first. This needs no `N`-invariant factor.
  `fpbs-twisted-level-graph-generates-cyclic-extension` proves that the graphing
  generates iff a random twisted return graph on the fibre group is connected.
  For the Bernoulli shift that graph is independent twisted level percolation.
  Route `fpbs-hyperbolic-3-manifold-fixed-price-via-twisted-levels` derives
  this claim from its connectivity. **Where it waits:**
  `fpbs-twisted-level-percolation-connected` is open. There are no finite
  clusters, so what remains is ruling out infinitely many infinite clusters on
  a nonamenable group, where Burton–Keane fails. The analogous graph for
  `F_2 = F_infinity semidirect Z` is disconnected, so the argument must use
  finite generation of the fibre group.
