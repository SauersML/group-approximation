---
rg: 2
id: pauli-kernel-integrates-and-has-quadratic-crossing
kind: claim
title: The Pauli kernel integrates to an exact edge gauge with a sharp quadratic crossing
artifacts:
  - research/edge-commutant-gauge-gives-pauli-normal-form.md
distinct_from:
  regular-trace-does-not-bound-iwahori-word-jacobian: that finds a vanishing raw singular value near the Pauli branch; this identifies the zero mode as an exact stabilizer orbit and computes the first transverse nonlinear term.
  iwahori-two-loci-have-zero-uniform-angle: that concerns the coupled reflected-BS and two-cubic loci near arithmetic packets; this is the complete local normal form of the single modular-to-Iwahori Pauli chart.
  same-core-involution-cubic-gauge-coercivity: that controls an endpoint gauge after a congruence core is authenticated; this computes a noncongruence finite-image stabilizer jump before any arithmetic endpoint has been selected.
---

Retain the two-dimensional family \(\rho_\theta\) in
**regular-trace-does-not-bound-iwahori-word-jacobian** and put
\(\theta_0=\pi/4\). At this point the two Iwahori word images coincide:
\[
 \rho_{\theta_0}(u)=\rho_{\theta_0}(e)=
 C=-{\sqrt3\over2}\sigma_y-{1\over2}\sigma_z.            \tag{PKN1}
\]
Let
\[
 H_0=-{i\over\sqrt6}C,\qquad W_s=\exp(sH_0).
\]
Then the exact modular representations
\[
 X_s=W_sXW_s^*,\qquad A_s=W_sA_{\theta_0}W_s^*
\]
have **literally constant** Iwahori restrictions:
\[
 X_sA_s=C,\qquad A_sX_sA_s^{-1}=C
 \quad\text{for every }s.                                \tag{PKN2}
\]
Their tangent at \(s=0\) is the full-support kernel vector
\(2^{-1/2}(B_1,B_1)\) from the preceding Jacobian calculation, up to the
common unit-speed normalization. Thus every quadratic, cubic, and higher
Taylor coefficient vanishes along the correctly integrated kernel path.
The kernel is an edge-commutant gauge orbit, not a transverse infinitesimal
deformation.

After quotienting this exact gauge, the Jacobian at \(\theta_0\) has squared
normal singular spectrum
\[
 \{\,4-\sqrt6,\ 2,\ 4+\sqrt6\,\}.                        \tag{PKN3}
\]
In particular its smallest normal singular value is
\(\sqrt{4-\sqrt6}>0\).

The stabilizer jump has a sharp two-parameter normal form. Compare the
Iwahori restriction of \(\rho_\theta\) with that of
\(W_s\rho_\theta W_s^*\), and let \(F(\theta,s)\) be the maximum normalized
Hilbert--Schmidt difference on \(u,e\). There are universal
\(c,C,\eta>0\) such that, whenever
\[
 |\theta-\theta_0|,\ |s|\leq\eta,
\]
one has
\[
 c\,|\theta-\theta_0|\,|s|
 \leq F(\theta,s)
 \leq C\,|\theta-\theta_0|\,|s|.                         \tag{PKN4}
\]
Locally the zero set is the union of the exact conjugacy axis \(s=0\) and
the enlarged edge-gauge axis \(\theta=\theta_0\). Hence
\[
 \operatorname{dist}\bigl((\theta,s),F^{-1}(0)\bigr)
 \leq C' F(\theta,s)^{1/2},                              \tag{PKN5}
\]
and exponent \(1/2\) is sharp along
\(|\theta-\theta_0|=|s|\to0\).

Therefore concatenating this flat direction alone cannot produce a
fixed-distance, vanishing-defect sequence: distance to the exact local
fiber still tends to zero at the square-root rate. The base representation
is the standard mod-two \(S_3\) representation and is not an arithmetic
endpoint for \(\operatorname{PSL}_2(\mathbb Z[1/2])\). Thus (PKN2) is an
exact **edge fiber**, not a new compatible arithmetic branch, and the root
remains open.

DERIVATION
edge-commutant-gauge-gives-pauli-normal-form
