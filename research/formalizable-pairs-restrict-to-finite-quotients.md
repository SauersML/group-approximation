---
rg: 2
id: formalizable-pairs-restrict-to-finite-quotients
kind: claim
title: A formalizable or stably formalizable pair restricts to a pair of the same kind on every finite quotient
distinct_from:
  marker-involution-is-formalizable-after-regrouping: that regroups along a finite-index subgroup, keeping all configurations but weakening equivariance; this restricts to the configurations invariant under a finite-index normal subgroup, keeping full equivariance of the quotient.
  formalizable-pairs-induce-polynomial-automorphisms-on-constants: that is the special case K = G, the constant configurations; this covers every finite-index normal subgroup.
artifacts:
  - research/artifacts/formalizability-finite-levels-and-z3-rigidity-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

Let `G` be a group, `K` a normal subgroup of finite index, and `(tau, sigma)` a formalizable pair on
`(F_2^n)^G`. Then the automata induced on `K`-invariant configurations, identified with
`(F_2^n)^(G/K)`, form a formalizable pair. The same holds for stably formalizable pairs.

With `finite-group-formalizability-equals-equivariant-automorphism`, every finite-level shadow of a
formalizable pair is a `G/K`-equivariant polynomial automorphism. On a host without proper
finite-index subgroups only the constant level survives.

*Why.* The substitution `X_(h,i) -> X_(hK,i)` is a ring homomorphism. It carries the rules to the
induced rules and the formal identity to a formal identity.

Artifact, Section 1, Theorem 2.
