---
rg: 2
id: q-lowdeg-removes-the-binary-three-atom-fence-but-not-morita-neutrality
kind: claim
title: Native qutrit low-degree testing removes the binary three-atom fence but not Morita neutrality
artifacts:
  - research/q-lowdeg-qutrit-pauli-scope-and-multiplicity-proof.md
distinct_from:
  reed-muller-pauli-stability-is-morita-neutral-to-nonlinear-occurrence-data: that treats the 2026 binary group-stability theorem and its power-of-two affine fence; this audits the native characteristic-three self-test and records exactly which part of the binary fence disappears.
  lin-independent-set-synchbcs-has-uniform-nonaffine-onehot-mass: that forces a positive nonaffine occurrence face in the source; this shows that qutrit Pauli rigidity still leaves that face in an arbitrary auxiliary algebra.
  multiplicity-conditioning-cannot-repair-the-moved-root-target-deficit: that computes the rank loss of the collected moved-root router after occurrence conditioning; this shows that changing the coordinate field does not control that occurrence block.
---

**EXACT SCOPE CORRECTION AND MORITA FENCE.**

Natarajan--Vidick, *Low-degree testing for quantum states, and a quantum
entangled games PCP for QMA*, arXiv:1801.03821v2, Theorem 3.2, applies to
generalized Pauli observables over every prime-power field
\(\mathbb F_q\) admitting a self-dual basis over its prime field. In
particular \(q=3\) is admissible, and the test has completeness one.

Therefore the power-of-two statement in
reed-muller-pauli-stability-is-morita-neutral-to-nonlinear-occurrence-data
is genuinely **binary-specific**. For commuting order-three coordinates,
ordinary word equations cut out affine subsets of \(\mathbb F_3^k\), and
a one-dimensional affine line has exactly three points. Native qutrit
coordinates can authenticate a three-outcome affine table.

This does not authenticate the Lin occurrence algebra. Theorem 3.2 is a
two-prover self-test up to local isometries and an arbitrary auxiliary
state. Its stated robustness is

\[
 \delta=\operatorname{poly}\!\left(
  \operatorname{poly}(p)\operatorname{poly}(\varepsilon)
  +\operatorname{poly}(d/q)
 \right).                                                \tag{QLM1}
\]

At fixed \(q=3\), this statement does not by itself give a vanishing
Hilbert--Schmidt stability modulus for a finite group presentation.
No qutrit analogue of the Chapman--Vidick--Yuen presentation-stability
translation is proved in that source.

More fundamentally, let \(\mathsf P_{3,k}\) be the generalized Pauli
group with central element \(J\) of order three. In the central-character
corner \(J=\omega\),

\[
 p_\omega C^*(\mathsf P_{3,k})p_\omega
 \cong M_{3^k}({\mathbf C}).                             \tag{QLM2}
\]

For every unital occurrence algebra \(A\),

\[
 p_\omega\big(C^*(\mathsf P_{3,k})\otimes_{\max}A\big)
 p_\omega
 \cong M_{3^k}({\mathbf C})\otimes_{\max}A.              \tag{QLM3}
\]

Every trace is uniquely \({\rm tr}_{3^k}\otimes\tau_A\); finite-dimensional
representations and Connes embeddability occur exactly when they do for
\(A\).

Thus generalized-Pauli coordinates may be perfect while a projection
\(1\otimes e\), \(e\in A\), is arbitrary. This is already built into the
auxiliary-state clause of self-testing. Forcing the occurrence projection
into the qutrit Pauli matrix factor produces a finite-dimensional source
model; leaving it in the auxiliary factor leaves it uncompiled.

The qutrit low-degree test is therefore useful for stabilizing a native
order-three coordinate table, and it removes the local binary
cardinality objection. It does not supply the mixed raw-\(S/T\)
range-authentication relation required to identify the initial support of
the three-line selector with the named nonaffine Lin projection. The
nonhyperlinear-group root remains open.

DERIVATION
q-lowdeg-qutrit-pauli-scope-and-multiplicity-proof
