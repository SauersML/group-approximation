---
rg: 2
id: pauli-tensor-charts-are-globally-congruence-captured
kind: claim
title: Every Pauli tensor chart is globally captured by its mod-two congruence base
artifacts:
  - research/collapse-pauli-branches-to-mod-two-congruence-base.md
distinct_from:
  pauli-kernel-integrates-and-has-quadratic-crossing: that computes the exact local edge-gauge crossing; this proves that arbitrary coupled pairs assembled from those charts are globally repairable after all endpoint and gauge freedoms are allowed.
  regular-trace-does-not-bound-iwahori-word-jacobian: that shows the raw single-vertex Jacobian can have a full-support small singular value; this shows that the resulting regular-character tensor models nevertheless lie uniformly close to the congruence locus.
  regular-iwahori-strict-congruence-exactification-is-false: that exhibits a rank-one boundary requiring flexible padding; this gives a same-dimensional congruence capture of the Pauli chart before the existing flexible pair repair is applied.
---

Let \(\rho_\theta\) be the two-dimensional Pauli representations and put
\(\theta_0=\pi/4\). Consider exact modular-vertex representations obtained
from finitely many blocks
\[
 \rho_{\theta_j}\otimes\eta_j,                           \tag{PTC1}
\]
where every \(\eta_j\) is an arbitrary exact congruence representation of
\(\operatorname{PSL}_2(\mathbb Z)\). Allow arbitrary multiplicities,
orthogonal direct sums, and one arbitrary unitary conjugation of the whole
sum. Define the physical RMS branch displacement
\[
 \Delta^2={1\over d}\sum_j
  2\dim(\eta_j)\,|\theta_j-\theta_0|^2.                  \tag{PTC2}
\]

For any pair \(\pi=(\pi_+,\pi_-)\) of such exact vertices, with unrelated
block data and unrelated unitary gauges, there are universal constants
\(K,C<\infty\) such that
\[
 D(\pi)\leq K\operatorname{def}(\pi)
          +C\max(\Delta_+,\Delta_-).                     \tag{PTC3}
\]
The constants are independent of all block multiplicities, tensor factors,
congruence levels, ambient dimensions, and conjugating gauges.

Consequently no dimension-growing fixed-distance countersequence can be
built from the full-support Pauli regular-character tensor charts while
their branch displacements and Iwahori defects tend to zero. This includes
the exact gauge family
\[
 W_s\rho_\theta W_s^*.
\]
On the sharp crossing
\(|s|\asymp|\theta-\theta_0|\), its edge displacement is comparable to
\(|\theta-\theta_0|^2\), while (PTC3) gives a global repair of order
\[
 O\!\left(\operatorname{def}^{1/2}\right).              \tag{PTC4}
\]
Thus the square-root exponent is the correct local price after the coupled
endpoint union and all gauge freedoms are restored.

The theorem does not control regular-character charts that stay a positive
RMS distance from every finite-dimensional congruence stratum. By
**capture-gap-localizes-to-regular-character-face**, such globally escaping
charts are the only remaining candidates. The root remains open.

DERIVATION
collapse-pauli-branches-to-mod-two-congruence-base
