---
rg: 2
id: candidate-amplification-envelope-proof
kind: route
title: Enumerate rational Cayley charts and amplify into a strict soundness window
target: candidate-amplification-envelope-closes-kleene
requires:
  - dimension-kleene-threshold-needs-amplification-envelope
  - post-candidate-nemesis-has-a-finality-dilemma
---

Rational unitaries are effectively dense in every `U(d)`.  One explicit
finite-atlas proof is as follows.  After multiplying a target unitary by a
rational point of the unit circle, chosen from the standard rational
parametrization and avoiding the finite exceptional spectrum, it lies in a
Cayley chart.  Approximate its skew-Hermitian Cayley inverse entrywise by a
matrix over `Q(i)`, preserving skew-Hermiticity, and apply the inverse Cayley
transform.  Matrix inversion over `Q(i)` is effective.  Multiplying back by
the rational phase gives an exactly unitary matrix over `Q(i)`.  Dovetailing
these charts therefore enumerates a dense family without an oracle for the
target tuple.

For a fixed finite presentation, relator defect and marked distance are
continuous functions of the finitely many generator matrices.  A canonical
hyperlinear microstate can consequently first be chosen with

```text
Def_P(U)<rho/8,       M_w(U)>beta+zeta                 (CAE3)
```

for some `zeta>0`, and then approximated by an enumerated rational tuple `Q`
in the same dimension so that

```text
Def_P(Q)<rho/4,       M_w(Q)>beta.                     (CAE4)
```

All comparisons can be performed effectively: word matrices over `Q(i)`
have rational squared normalized Hilbert--Schmidt norms, and the search uses
strict rational inequalities (squaring positive sides when necessary).

By `(CAE2)`, some `k` satisfies `delta(c_Q,k)>rho/2`; this follows from the
definition of supremum even if it is not attained.  Since the values
`delta(c_Q,k)` and `rho` are computable rationals, dovetailing over `k` finds
one.  Tensor amplification `Q tensor I_k` preserves both normalized-HS
defect and marked distance exactly.  Thus

```text
Def_P(Q tensor I_k)<rho/4<delta(c_Q,k),
M_w(Q tensor I_k)>beta.                                (CAE5)
```

Acceptance completeness makes the verifier halt.  Final-presentation
soundness then gives marked value at most `alpha`, contradicting
`beta>alpha`.

There is no post-candidate update in this proof.  If halting appends a new
packet, `Q tensor I_k` was tested only against the old presentation and the
argument is invalid by the finality dilemma.  A valid implementation must
interpret halting as selecting a branch already encoded in the fixed
presentation.

