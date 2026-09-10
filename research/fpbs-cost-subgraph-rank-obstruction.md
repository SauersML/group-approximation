---
rg: 2
id: fpbs-cost-subgraph-rank-obstruction
kind: claim
title: Optimized subgraph cost cannot be a restriction-consistent submodular rank
artifacts:
  - research/artifacts/fpbs/docs/cost-rank-duality.md
---

For every r>=2, every essentially free pmp action of F_r x Z^2
has bounded-degree subgraphings A,B with optimized relation costs
C(R_A)=C(R_B)=C(R_(A union B))=1 and
C(R_(A intersect B))=r. Thus F |-> C(R_F) is neither monotone
nor submodular. No universally monotone or submodular graphing-rank
assignment can simultaneously attain total relation cost and be
consistent under restriction to edge subsets.

The intersection treeing has zero relative completion cost in
the ambient relation, but every graphing retaining its edges
costs at least r. This separates cheap completion from replacement
at optimal cost. The artifact proves these statements and explains
why they do not refute the broader ambient-dependent cost-matroid
question or resolve Fixed Price.

Status represents a written deduction from imported cost theorems,
not Lean or independent mathematical verification.
