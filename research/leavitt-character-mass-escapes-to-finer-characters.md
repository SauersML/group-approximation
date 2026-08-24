---
rg: 2
id: leavitt-character-mass-escapes-to-finer-characters
kind: claim
title: Leavitt character mass escapes to finer characters as the matrix dimension grows
distinct_from:
  bare-self-copy-mf-calibration: that exhibits one torsion-free finitely presented operator-MF group in which a nontrivial compression defect survives a norm corona, calibrating the phase boundary by example; this identifies the mechanism by which one specific finite-dimensional argument, the Leavitt branch multiplicity doubling, fails to transfer, and does so without exhibiting a group.
  character-diracization-limit: that drives every character to the regular character of its scalar-kernel quotient using conjugate tensor powers; this is about where the multiplicity mass of the branch-doubling argument goes as the matrix dimension grows, and its compatibility with a diffuse CAR/UHF limit, with no tensor power taken.
  compression-defect-dies-in-finite-dimensions: that is a theorem about honest finite-dimensional representations; this is a negative statement about approximate finite-dimensional microstates, saying that this particular mechanism has no microstate analogue.
  atomic-morita-return-kills-finite-order-mf-mark: that is the conditional collapse theorem which does succeed at the microstate level, given a coefficient return on a prescribed spectral atom; this explains why such a return has to be assumed rather than derived from the finite-dimensional mechanism.
artifacts:
  - research/artifacts/property-t-free-atomic-leavitt-amr-2026-08-24.md
  - GroupApproximation/Criterion/FiniteDimensionalKill.lean
---

**ESTABLISHED OBSTRUCTION.**  The multiplicity-doubling mechanism of
`leavitt-heisenberg-branch-doubles-character-multiplicity` does **not** pass
to matrix microstates.

In an honest finite-dimensional representation the character set is finite,
so a maximal-multiplicity character exists and `(MD)` contradicts it.  In a
sequence of approximate models of growing dimension the character set is not
fixed: the mass counted by `m` can escape to **increasingly fine
characters**, so no maximum is available to contradict.  The corresponding
diffuse limit is perfectly compatible with infinite CAR/UHF-type
representations, in which the doubling relation `(MD)` holds and is
harmless.

Two consequences worth stating separately.

1. **Full orthogonal self-copy, elementary commutator calculus, and normal
   generation are jointly insufficient** at the microstate level.  Adding
   more of the same algebra does not close the gap, because the escape is not
   an algebraic failure -- every relation still holds -- but a failure of
   compactness in the character space.

2. **Replacing property (T) by hidden spectral-gap language does not solve
   it.**  A gap hypothesis phrased on the character side buys exactly the
   maximum that the escape destroys, so it is not a weakening of (T) but a
   restatement of the missing input.

What is genuinely needed is a **finite-coordinate return mechanism**: some
statement that pins the mass onto a bounded number of coordinates, so that a
maximum exists again.  That is the role played by
`binary-leavitt-atomic-morita-return`, which remains open, and it is why the
established endpoint `atomic-morita-return-kills-finite-order-mf-mark` takes
the return as a hypothesis rather than deriving it.

## Attempts

- Uniformizing `(MD)` over the model sequence: the doubling constant is
  already uniform, so this changes nothing; the failure is in the index set,
  not the constant.
- Coarsening the character space to a fixed finite quotient before applying
  `(MD)`: the translation `tau` is not constant on the coarsening, so the
  companion character can collapse onto the original and the doubling is
  lost.
