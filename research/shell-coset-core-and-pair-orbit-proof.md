---
rg: 2
id: shell-coset-core-and-pair-orbit-proof
kind: route
title: Retain the shell stabilizer as a core-free subgroup and identify the remaining double-coset condition
target: shell-coset-induction-preserves-core-freeness
requires:
  - shell-cantor-embeddings-are-finite-germ-extensions
  - shell-finite-point-stabilizers-are-finitely-generated
  - decidable-inputs-have-computable-non-fp-shell-envelopes
  - clapham-fp-embedding-preserves-word-problem
  - type-a-action-gives-boone-higman-for-subgroups
artifacts:
  - research/artifacts/boone-higman-spatial-overgroup-and-coset-gate-2026-09-08.md
---

Since Omega is dense in C, its E action is faithful. Transitivity
identifies Omega with E/H, so core_E(H)=1. For E<=Gamma,

    core_Gamma(H) subset core_E(H)=1.

This is the kernel of the Gamma action on Gamma/H. In particular
there is no quotient by an unknown normal kernel in this construction.
The point stabilizers are conjugates of H, which is finitely generated
by the required shell stabilizer result. The restriction to the
subset E/H gives the original E action; other E orbits can appear.

For a transitive action, orbits on ordered pairs are in bijection
with H double cosets, by moving the first point to H. There is one
diagonal orbit. Passing from ordered distinct pairs to two-element
subsets identifies at most two orbits at a time. Thus finite bi-index
is exactly the finite two-element-orbit condition of type (A).
If Gamma is finitely presented, the other conditions are already
verified, and the required embedding theorem applies.

For a decidable input, choose the computable free-near enumeration
from the required existence claim. Its E is finitely generated and
has decidable word problem, so Clapham gives an embedding in a
finitely presented Gamma with decidable word problem. This establishes
availability of overgroups, not availability of the particular
double-coset finiteness needed above. Indeed E itself is not finitely
presented for this enumeration, so this is a proper enlargement.
