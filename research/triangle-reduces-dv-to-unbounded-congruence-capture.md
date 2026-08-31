---
rg: 2
id: triangle-reduces-dv-to-unbounded-congruence-capture
kind: route
title: Combine mixed-congruence repair with the generalized-metric triangle inequality
target: dv-distance-is-defect-plus-congruence-capture
requires:
  - mixed-crt-iwahori-repair-is-labeled-pure-dyadic-rounding
  - odd-label-stabilization-has-uniform-repair
  - finite-dimensional-dual-of-sl2-z-inverse-two-is-odd-congruence
  - iwahori-uniform-infinitesimal-rigidity
  - mersenne-phases-far-from-all-frozen-core-endpoints
  - mersenne-phases-have-explicit-exact-core-bend
---

# Combine mixed-congruence repair with the generalized-metric triangle inequality

## 1. One constant for every exact congruence pair

Let \(\rho=(\rho_+,\rho_-)\in\mathcal C\). Write the two levels as
\[
n_+=2^a m_+,\qquad n_-=2^b m_-,
\qquad m_+,m_-\ \text{odd}.
\]
The CRT decomposition in
**mixed-crt-iwahori-repair-is-labeled-pure-dyadic-rounding** writes the
common edge quotient as a pure-dyadic restriction diagram times its finite
odd label set. Its Selberg estimate charges the weighted restriction
mismatch by the square of the Hilbert--Schmidt defect.

The theorem **odd-label-stabilization-has-uniform-repair** supplies one
integer-Hoffman constant \(H_{\mathrm{mix}}\), independent of \(a,b\), the
odd levels, all odd-label dimensions, and the ambient dimension. Substitution
in (MCR6) gives a finite constant
\[
K_{\mathrm{cong}}
 =
 \frac8\kappa+
 \left(\frac{2\sqrt2}{\kappa}
       +\frac{32\sqrt2}{\kappa^2}\right)
 \sqrt{H_{\mathrm{mix}}},                               \tag{1}
\]
where \(\kappa\) is the fixed congruence Selberg constant. Thus there is a
compatible pair \(\widetilde\rho\), in the same dimension as \(\rho\), with
\[
d_2(\rho,\widetilde\rho)
 \le K_{\mathrm{cong}}\operatorname{def}(\rho).          \tag{2}
\]
No conductor cutoff occurs in (1).

## 2. Defect is Lipschitz in the generalized metric

Let the fixed modular generating sets used in \(d_2\) be \(S_+\) and
\(S_-\). For every \(b\) in the fixed Iwahori defect set, choose words for
\(b\) in \(S_+\) and for \(\sigma(b)\) in \(S_-\), and let \(L_B\) be the
maximum of their lengths.

For any two exact vertex pairs \(\pi,\rho\), possibly of different
dimensions, put
\[
\delta=d_2(\pi,\rho).
\]
Zero-pad the smaller matrices as in Dogon--Vigdorovich's generalized metric.
A product of zero-padded matrices is the zero-padding of the product, and
every factor has operator norm at most one. The usual telescoping sum
therefore gives
\[
d_2(\pi_+(b),\rho_+(b))\le L_B\delta,\qquad
d_2(\pi_-(\sigma b),\rho_-(\sigma b))\le L_B\delta.
\]
The middle term obtained by padding the two matrices of \(\pi\) can only
decrease its normalized Hilbert--Schmidt norm. Hence
\[
\operatorname{def}(\rho)
 \le \operatorname{def}(\pi)+2L_B\delta.                \tag{3}
\]

## 3. Triangle reduction

Choose \(\rho\in\mathcal C\) with
\[
d_2(\pi,\rho)\le A_{\mathrm{cong}}(\pi)+\varepsilon.
\]
Apply (2), then (3), and use the triangle inequality:
\[
\begin{aligned}
D(\pi)
 &\le d_2(\pi,\rho)+d_2(\rho,\widetilde\rho)\\
 &\le \delta+
 K_{\mathrm{cong}}\bigl(\operatorname{def}(\pi)+2L_B\delta\bigr)\\
 &=K_{\mathrm{cong}}\operatorname{def}(\pi)
 +(1+2K_{\mathrm{cong}}L_B)\delta.
\end{aligned}
\]
Letting \(\varepsilon\downarrow0\) proves the upper bound in (DCC2).

Every compatible finite-dimensional pair comes from a finite-dimensional
representation of \(\operatorname{SL}_2(\mathbb Z[1/2])\).
By **finite-dimensional-dual-of-sl2-z-inverse-two-is-odd-congruence**, it
has finite odd-congruence image. Therefore the compatible locus is contained
in \(\mathcal C\), and
\[
A_{\mathrm{cong}}(\pi)\le D(\pi),                        \tag{4}
\]
which proves the lower bound.

Equations (DCC2) and (4) give the equivalence of moduli. If
\(A_{\mathrm{cong}}(\pi)\le g(\operatorname{def}\pi)\) with
\(g(x)\to0\), then
\[
D(\pi)\le K_{\mathrm{cong}}x+
 (1+2K_{\mathrm{cong}}L_B)g(x).
\]
Conversely any modulus for \(D\) is automatically one for
\(A_{\mathrm{cong}}\) by (4).

## 4. Local angle and frozen-core audit

At a compatible congruence point, the derivative of the edge mismatch is
already uniformly bounded below modulo its exact kernel by
**iwahori-uniform-infinitesimal-rigidity**. Its proof contains separate
uniform estimates for cuspidal cohomology, Eisenstein residues, and
coboundaries. Thus no unbounded Hecke or Iwahori type inside the congruence
locus can make the local same-dimension cosystolic angle vanish.

There is no conflict with the global zero-angle and frozen-core examples.
The Mersenne construction fixes \(R,T\) and finds a phase \(X_\eta\) far
from every exact endpoint in that relative slice. But its diagonal gauge
\(U_\eta\) satisfies
\[
[U_\eta,R]=0,\qquad
\|U_\eta T U_\eta^*-T\|_2^2=\frac8{3n},
\]
and \((U_\eta X_0U_\eta^*,R,U_\eta T U_\eta^*)\) is an exact congruence
endpoint. The ordinary Dogon--Vigdorovich metric permits this core movement,
so the fixed-core gap is not a congruence-capture gap.

The remaining statement (DCC3) must force arbitrary exact modular
representations, including noncongruence and infinite-image ones, toward
\(\mathcal C\). This is a global representation-selection theorem, not full
Hilbert--Schmidt stability of either vertex group and not a missing
same-dimensional congruence angle.
