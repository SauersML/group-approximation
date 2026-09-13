---
rg: 2
id: colored-cfi-rung-is-the-solution-group-case
kind: claim
title: On colored CFI graphs the isomorphism rung is literally the solution-group endpoint
artifacts:
  - research/artifacts/ex-nh-mipstar-quantum-symmetry-rung-2026-09-12.md
distinct_from:
  lcs-tracial-nonru-gap-gives-qc-qa-cfi-graph-gap: that transfers the linear-system gap to plain CFI graph pairs through a hereditary *-equivalence of games; this identifies the colored CFI isomorphism algebra *-isomorphically with the linear-system algebra, and the quantum automorphism group with a group dual.
  closure-safe-support-is-exactly-the-colored-iso-rung: that characterizes which bisynchronous gaps feed the colored rung; this shows that on colored CFI pairs the rung carries no more than the solution group, so the rung can only go beyond groups on colored digraphs whose quantum symmetry is not a group dual.
---

**ESTABLISHED** by `colored-cfi-rung-is-the-solution-group-case-citation`.

Roberson--Schmidt (arXiv:2111.12362v1, J. London Math. Soc. 106 (2022)) prove
two things.  Let `M in F_2^(m x n)` and `b in F_2^m`, and let `G(M,b)` be their
colored graph.  Its vertices are the local solutions `(k, alpha)` of each
equation.  Vertex colours record the equation, and edge colours record the
difference `alpha △ beta` on shared variables.

1. `C(Qut(G(M,b))) ≅ C^*(Gamma_0(M))` as compact quantum groups: the quantum
   automorphism group is the dual of the homogeneous solution group
   (Theorem 3.8).
2. `Iso(G(M,b), G(M,b')) ≅ A(M, b+b')`, the universal C*-algebra of the linear
   system `Mx = b+b'` (Theorem 6.7).  Their Definition 6.5 notes that
   `A(M,c) ≅ p C^*(Gamma(M,c))` with `p = (1-gamma)/2`.

**Consequences for the rung.**  Take `b' = 0`.  A tracial state on
`Iso(G(M,b), G(M,0))` is a tracial state on the linear-system algebra, and a
unital *-homomorphism into `R^U` is an `R^U` model of the system.  So:

- colored `G(M,b) ≅_qc G(M,0)` but not `≅_qa` iff `Mx = b` is tracially
  satisfiable and not `R^U`-satisfiable;
- by `lcs-tracial-ru-gap-equiv-nonhyperlinear`, this is iff there is a
  finitely presented nonhyperlinear group.

On colored CFI pairs the quantum symmetries of both sides are group duals.
So the non-Connes-embeddable Kac quantum group supplied by
`closure-safe-support-is-exactly-the-colored-iso-rung` would come from a
solution group.  The rung goes strictly beyond groups only on colored
digraph pairs whose quantum automorphism groups are genuinely quantum, i.e.
not group duals.
