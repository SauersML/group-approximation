---
rg: 2
id: finite-normal-clause-orbit-bcs-compiler
kind: claim
title: Compile the non-CE BCS into one finite normal orbit of phase-safe clause words
distinct_from:
  central-word-state-face-compiler: that permits any whole-face decoder and asks separately for quantitative soundness; this imposes conjugation invariance of the aggregate clause Hamiltonian, which makes quantitative soundness automatic by Haar twirling
  bcs-projective-kernel-phase-compilation: that seeks binomial relations in a projective GNS kernel; this permits a finite conjugation orbit whose aggregate, rather than each individual word, is invariant
  finite-morita-toricization-cannot-encode-nonaffine-support: that rules out representation-functorial finite-Morita truth-table compilation; this asks for a state-face implication and may use a nonfunctorial global coupling
---

**OPEN.**  For the fixed BCS from
`non-ce-bcs-has-robust-approximate-energy-gap`, construct a finite
phase-safe toric target with decoded unitary observables `z_x` and clause
unitaries `u_1,...,u_m` such that, for

```text
D=sum_i (u_i-1)^*(u_i-1),
H_B=sum_(R in R_B)R(z)^*R(z),                           (FNO1)
```

the following hold.

1. The perfect tracial BCS model extends to a target representation fixing
   all `u_i` and retaining the marked scalar phase.
2. Conjugation by every `z_x` permutes the finite multiset
   `{u_i,u_i^*:1<=i<=m}`.  Equivalently, `[D,z_x]=0` for every `x`.
3. Every target state `phi` which is tracial on `C*(z_x)` and has
   `phi(D)=0` satisfies `phi(H_B)=0`.
4. The target clauses remain torically determined after normal closure, and
   their normal closure meets the finite phase group trivially.

Conditions 1, 3, and 4 are exact algebraic requirements.  Condition 2 is the
new finite symmetry actuator: it need not make any individual nonlinear
predicate word central.  By
`conjugation-invariant-clause-energy-twirls-vector-states`, Conditions 2 and
3 force a uniform positive lower bound on the clause energy of every
finite-dimensional target vector state.  Thus this claim would establish all
three properties of `central-word-state-face-compiler`.

## Attempts

- Making each predicate word central is stronger than Condition 2 and fails
  by the forbidden central-character sectors `(CWA9)` in
  `central-word-state-face-compiler`.
- A finite local reversible packet whose word merely agrees with the
  nonlinear predicate on selected types fails by finite-Morita induction;
  the normal orbit must obtain its exact zero-face implication only after the
  contexts are globally coupled.
- Product-word stabilizers cannot cut out one forbidden Boolean rectangle.
  The orbit therefore cannot consist only of independent local product
  clauses.
- Taking all conjugates in a free player group gives an infinite orbit and
  no finite game.  The missing construction is a finite quotient action on
  the clause module which preserves the perfect nonclassical state without
  reintroducing all forbidden selector characters.

