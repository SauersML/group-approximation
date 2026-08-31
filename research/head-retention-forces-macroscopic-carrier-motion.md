---
rg: 2
id: head-retention-forces-macroscopic-carrier-motion
kind: claim
title: A Jacobson head forces macroscopic motion away from every Toeplitz carrier
distinct_from:
  toeplitz-folner-compressions-cannot-retain-jacobson-head: that treats the carrier tuple itself; this gives a quantitative lower bound for completely arbitrary generator perturbations
  presentation-defect-does-not-control-off-commutant-mass: that shows off-commutant mass cannot be upper-bounded by relator defect; this lower-bounds total carrier motion when the head is retained
  pauli-swap-coherence-reduces-to-the-commutant-gate: that kills discrete two-sheet swaps; this rules out infinitesimal continuous rotations without assuming a block grading
---

Fix the standard presentation, head word `w`, and Toeplitz carrier

```text
A_s=rho(theta_N(s)).
```

For an arbitrary unitary tuple `U=(U_s)` on the same Hilbert space, set

```text
eta(U,A)=max_(s in Sigma)||U_s-A_s||_2.
```

There are constants `C_0,C_1<infinity`, depending only on the fixed
presentation and not on `N`, `rho`, or the matrix dimension, such that

```text
||w(U)-I||_2 <= C_0 delta(U)+C_1 eta(U,A).              (HMC1)
```

Equivalently, whenever `||w(U)-I||_2>=epsilon`,

```text
eta(U,A) >= (epsilon-C_0 delta(U))/C_1.                 (HMC2)
```

Thus no head-retaining Jacobson microstate can be obtained from the
Toeplitz finite section by generator perturbations tending to zero in
normalized Hilbert--Schmidt norm. This includes every infinitesimal
two-sheet `SU(2)` rotation, whether or not it lies in the carrier
commutant.

Together with `pauli-swap-coherence-reduces-to-the-commutant-gate`,
`(HMC2)` sharply locates the smallest continuous mixed-isotype survivor:
at least one generator must have a macroscopic, genuinely nonmonomial
two-sheet rotation. The result does not rule out such a rotation.

DERIVATION
word-telescoping-transfers-the-endpoint-conjugacy-proof
