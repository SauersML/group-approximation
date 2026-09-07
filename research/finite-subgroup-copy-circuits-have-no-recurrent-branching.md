---
rg: 2
id: finite-subgroup-copy-circuits-have-no-recurrent-branching
kind: claim
title: A finite copying circuit of finite-subgroup projectives can recur only along closed simple cycles
distinct_from:
  finite-subgroup-corners-have-invariant-basis-number: that compares multiple copies of one projective; this allows different states and an arbitrary finite directed graph of copying equations.
  lifted-trace-detects-finite-subgroup-projectives: that provides the additive rank invariant; this classifies the possible recurrent graph components under exact module-decomposition identities.
---

Let S=F_p[G]. For each vertex v of a finite directed multigraph, let
P_v be a nonzero finite direct sum of projectives induced from finite
subgroups of G. Suppose there are exact S-module isomorphisms

    P_v ~= direct_sum_(edges v->w) P_w.                 (FCC1)

Then every strongly connected component containing a directed cycle is
a simple directed cycle with edge multiplicity one, and has no outgoing
edge to any other vertex. The remaining vertices form an acyclic graph
feeding into these cycles. In particular, a strongly connected circuit
cannot contain a branching vertex.

All implementing maps may have arbitrary support in the ambient group.
The obstruction concerns the projective state modules, not locality of
the transitions. It excludes recurrent amplification by exact copying
of these modules, including a cyclic circuit made from different finite
packets. It does not exclude arbitrary verification circuits: checking
identities, nonlinear cellular automata, and chain complexes need not
satisfy the direct-sum equations (FCC1).
