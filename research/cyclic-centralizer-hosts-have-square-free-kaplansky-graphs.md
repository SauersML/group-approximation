---
rg: 2
id: cyclic-centralizer-hosts-have-square-free-kaplansky-graphs
kind: claim
title: In a torsion-free group with cyclic centralizers, the Kaplansky graph of a support-3 zero divisor has no cycle of length at most four
distinct_from:
  kaplansky-graph-squares-force-central-trefoil-generators: that derives a central trefoil structure from a 4-cycle in any torsion-free host; this applies it to hosts with cyclic centralizers, where the structure cannot occur.
  zero-divisor-host-is-not-virtually-compact-special: that excludes ambient host classes outright; this constrains the Kaplansky graph in a host class where the conjecture is open.
  f2-support-three-zero-divisors-need-support-at-least-22: that is a support bound over F_2 in every torsion-free group; this is a girth bound over every field in a restricted host class.
artifacts:
  - research/artifacts/zds-three-support-theory-2026-09-13.md
---

**ESTABLISHED.** Let `G` be a torsion-free group in which the centralizer of
every nontrivial element is cyclic. Let `k` be a field and `alpha, beta`
nonzero in `k[G]` with `alpha beta = 0`, `|supp alpha| = 3` and
`|supp beta|` least. Then in the Kaplansky graph `K_k(alpha, beta)`:
- no two vertices are joined by two different relations;
- there is no 3-cycle;
- there is no 4-cycle.

So every cycle has length at least `5`.

**Hosts.** Torsion-free hyperbolic groups have cyclic centralizers of
nontrivial elements (a standard fact). These include:
- the generalized Rips--Segev groups, which Steenbock proved hyperbolic, as
  recorded in the introduction of Arzhantseva--Steenbock (arXiv:1407.2441);
- the torsion-free hyperbolic groups without the unique product property of
  Arzhantseva--Steenbock Thm `main`.

Whether Rips--Segev groups satisfy the zero-divisor conjecture is an open
question stated by Steenbock (arXiv:1307.0981, introduction). The property
passes to subgroups, so it applies to `<supp alpha>`.

**Why the host class matters.** For 4-cycles this is sharp at the level of
single relations: each of the nine 4-cycle relation classes that survive in
every torsion-free host defines the trefoil group, which is torsion-free and
not elementary amenable, and has a nontrivial center.

DERIVATION
[[cyclic-centralizer-hosts-square-free-proof]]
