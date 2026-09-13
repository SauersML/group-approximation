---
rg: 2
id: fpbs-hyperbolic-nonunimodular-critical-l2-gap
kind: claim
title: Hyperbolic graphs and graphs with nonunimodular automorphism subgroups have p_c below p_(2->2)
distinct_from:
  fpbs-hyperbolic-and-nonunimodular-nonuniqueness: that imports p_c<p_u for the same two classes; this imports the stronger strict l2 gap p_c<p_(2->2), which the pivotal kernel bounds need.
  fpbs-critical-l2-implies-nonuniqueness: that is the implication from an l2 hypothesis to nonuniqueness; this imports the l2 hypothesis itself for two classes of graphs.
  fpbs-nonamenability-bounds-critical-connectivity-operator: that conjectures an l2 bound on every nonamenable transitive graph; this imports a strict gap only for Gromov hyperbolic graphs and graphs with a quasi-transitive nonunimodular automorphism subgroup.
---

These are published theorems of Hutchcroft, imported by citation. Let `G` be a
connected, locally finite graph. Then `p_c(G) < p_(2->2)(G)` in either of two
cases:

* `G` is quasi-transitive, nonamenable and Gromov hyperbolic;
* `Aut(G)` has a quasi-transitive nonunimodular subgroup.

Here `p_(2->2)` is the supremum of the parameters `p` at which the
connectivity matrix `tau_p(u,v)` is bounded on `l2(V)`.
