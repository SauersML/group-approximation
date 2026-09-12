---
rg: 2
id: collapse-pauli-branches-to-mod-two-congruence-base
kind: route
title: Replace every Pauli block by its mod-two base and invoke the capture triangle
target: pauli-tensor-charts-are-globally-congruence-captured
requires:
  - pauli-kernel-integrates-and-has-quadratic-crossing
  - dv-distance-is-defect-plus-congruence-capture
  - odd-label-stabilization-has-uniform-repair
---

# Collapse every branch block to an exact mixed-congruence vertex

The map
\[
 \theta\longmapsto
 \rho_\theta=(X,A_\theta)
\]
is analytic on a compact interval. Hence, in the fixed modular-generator
metric, there is a universal \(L_0\) such that
\[
 d_2(\rho_\theta,\rho_{\theta_0})
 \leq L_0|\theta-\theta_0|.                              \tag{1}
\]
Tensoring with a unitary representation preserves normalized
Hilbert--Schmidt distance:
\[
 \|(U-V)\otimes Z\|_{2}= \|U-V\|_{2}
 \quad\text{for unitary }Z.                              \tag{2}
\]
Distance is Pythagorean on orthogonal direct sums. Therefore replacing every
block (PTC1) by
\[
 \rho_{\theta_0}\otimes\eta_j                            \tag{3}
\]
moves the whole vertex by at most \(L_0\Delta\). Applying the same arbitrary
global conjugating unitary before and after the replacement leaves this
estimate unchanged.

The base \(\rho_{\theta_0}\) is the standard representation of the
mod-two quotient
\[
 \operatorname{PSL}_2(\mathbb Z/2\mathbb Z)\cong S_3.
\]
If \(\eta_j\) factors through level \(m_j\), then (3) factors through the
joint reduction of level \(\operatorname{lcm}(2,m_j)\). A finite direct sum
of the blocks factors through one common multiple of those levels.
Consequently the replacement is an exact congruence representation of the
modular vertex. This remains true after arbitrary unitary conjugation.

Perform the replacement independently on the two vertices. By definition
of congruence-capture distance,
\[
 A_{\mathrm{cong}}(\pi)
 \leq L_0\max(\Delta_+,\Delta_-).                        \tag{4}
\]
Now apply **dv-distance-is-defect-plus-congruence-capture**:
\[
 \begin{aligned}
 D(\pi)
 &\leq K_{\mathrm{cong}}\operatorname{def}(\pi)\\
 &\quad +(1+2K_{\mathrm{cong}}L_B)
       A_{\mathrm{cong}}(\pi)\\
 &\leq K_{\mathrm{cong}}\operatorname{def}(\pi)
       +(1+2K_{\mathrm{cong}}L_B)L_0
        \max(\Delta_+,\Delta_-).
                                                               \tag{5}
 \end{aligned}
\]
This is (PTC3).

For the exact gauge slice in the preceding Pauli normal form, retain the same
conjugator \(W_s\) when making replacement (3). Thus arbitrary coset or
endpoint gauge cannot undo (4); it is already absorbed into the nearby
congruence vertex. If a coupled assembly has
\[
 |s|\asymp|\theta-\theta_0|=\delta
 \quad\text{and}\quad
 \operatorname{def}(\pi)\asymp\delta^2,
\]
as in the sharp product crossing, then \(\Delta=O(\delta)\) and (5) gives
\[
 D(\pi)=O(\delta)=O(\operatorname{def}(\pi)^{1/2}).
\]
This is the conditional square-root statement (PTC4). It asserts no
quadratic defect for a pair carrying an additional opposite-Iwahori
mismatch.
