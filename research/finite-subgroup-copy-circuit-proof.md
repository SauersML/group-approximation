---
rg: 2
id: finite-subgroup-copy-circuit-proof
kind: route
title: A minimum positive lifted rank forces one successor throughout every recurrent component
target: finite-subgroup-copy-circuits-have-no-recurrent-branching
requires:
  - lifted-trace-detects-finite-subgroup-projectives
---

The lifted trace assigns each P_v a positive rational number r_v,
viewed inside Z_p. Additivity in (FCC1) gives

    r_v=sum_(edges v->w) r_w.

These are equalities of rational numbers because Q embeds in Q_p, so
we may use their ordinary rational order. Each vertex has an outgoing
edge, since r_v>0.

Let C be a strongly connected component containing a directed cycle.
Choose v in C with r_v minimal among the vertices of C. It has at
least one outgoing edge v->w inside C. For this edge r_w>=r_v. Since
all ranks are positive, the displayed equality forces r_w=r_v and
forces v->w to be the only outgoing edge of v in the entire graph.
The same argument applies to w and every subsequent successor.

This deterministic forward walk eventually forms a cycle. Strong
connectivity requires every vertex of C to be reachable from v, but
the unique-successor property shows that only this walk is reachable.
Strong connectivity also requires a return to v, so there is no initial
tail. Thus the walk is a simple cycle containing all of C. Each vertex
has precisely one outgoing edge, including multiplicity, and no edge
leaves C.

Any vertex outside such components is not on a cycle, so the induced
graph on these vertices is acyclic. Because all vertices have a
successor and the graph is finite, every forward walk eventually
reaches one of the closed cycles. This proves the classification.

No ordering of Z_p and no positivity for arbitrary ambient projectives
is assumed. The positive rational values supplied by finite-subgroup
induction are the entire reason the argument applies.
