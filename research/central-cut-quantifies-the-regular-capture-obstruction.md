---
rg: 2
id: central-cut-quantifies-the-regular-capture-obstruction
kind: route
title: Cut the ultraproduct character and compare blockwise Hilbert--Schmidt distance
target: capture-gap-localizes-to-regular-character-face
requires:
  - bs14-character-split-leaves-only-the-regular-microstate-face
  - finite-dimensional-dual-of-sl2-z-inverse-two-is-odd-congruence
  - regular-iwahori-exactification-is-regular-branch-liftability
  - dv-distance-is-defect-plus-congruence-capture
---

# Cut the character and retain the metric gap

## 1. The central character cut

Let \(\omega\) be a free ultrafilter along a subsequence on which the lower
limit in (RCL1) is realized. Since the edge defects tend to zero, the two
exact vertex homomorphisms glue in
\[
 \mathcal M=\prod_\omega(M_{d_n},\operatorname{tr}_{d_n})
\]
to a homomorphism
\[
 \Pi:A\longrightarrow U(\mathcal M).                     \tag{1}
\]
Put \(N=\Pi(A)''\).

By Peterson--Thom character rigidity in the form recorded in
**bs14-character-split-leaves-only-the-regular-microstate-face**, there is a
central projection \(z_{\mathrm{fin}}\in N\) such that the normalized
character on \(Nz_{\mathrm{fin}}\) is a direct integral of finite-quotient
characters, while on
\[
 z_{\mathrm{reg}}=1-z_{\mathrm{fin}}
\]
it is \(\delta_e\). Put \(r=\tau(z_{\mathrm{reg}})\).

Lift \(z_{\mathrm{reg}}\) to projections \(p_n\in M_{d_n}\), changing ranks
by \(o(d_n)\) if necessary. Centrality gives
\[
 \|[p_n,\pi_{n,\pm}(s)]\|_2\longrightarrow0              \tag{2}
\]
for every fixed vertex generator. Polar compression turns the two corners
into unitary approximate vertex representations with \(o(1)\) error.
Same-dimensional Hilbert--Schmidt stability of the modular vertices, one of
the established inputs in
**regular-iwahori-exactification-is-regular-branch-liftability**, perturbs
them by \(o(1)\) to exact vertex representations. Denote the exact regular
corner by
\[
 \kappa_n:V_+*V_-\longrightarrow U(e_n),
 \qquad e_n=\operatorname{rank}p_n+o(d_n).                \tag{3}
\]
Equations (1)--(3) show
\[
 e_n/d_n\longrightarrow r,\qquad
 \operatorname{def}(\kappa_n)\longrightarrow0,            \tag{4}
\]
and the induced ultraproduct character of (3) is \(\delta_e\).

On the complementary corner the GNS algebra is hyperfinite. The hyperfinite
HS-stability step in
**bs14-character-split-leaves-only-the-regular-microstate-face** corrects
that compressed microstate, flexibly and at \(o(1)\) cost, to genuine
finite-dimensional representations of \(A\). By
**finite-dimensional-dual-of-sl2-z-inverse-two-is-odd-congruence**, those
representations are odd-congruence endpoints.

## 2. Blockwise metric inequalities

Normalized Hilbert--Schmidt distance is Pythagorean on orthogonal direct
sums. If a tuple on an \(e_n\)-dimensional block is changed by normalized
distance \(a_n\), its contribution in dimension \(d_n\) is
\[
 \sqrt{e_n/d_n}\,a_n.                                    \tag{5}
\]
The \(o(d_n)\) rank changes made above contribute \(o(1)\).

Choose asymptotically minimizing congruence comparisons for \(\kappa_n\),
and direct-sum them with the congruence corrections of the finite corners.
Equations (4) and (5) give
\[
 \liminf_n A_{\mathrm{cong}}(\pi_n)
 \leq
 \sqrt r\,\liminf_n A_{\mathrm{cong}}(\kappa_n).           \tag{6}
\]
The same statement follows first for a chosen subsequence realizing the
right-hand lower limit and then for the original lower limit. Combining
(RCL1) with (6) proves (RCL2).

For the rank estimate, replace the whole regular corner instead by
\(e_n\) copies of the trivial congruence representation. Two unitary
generator matrices are at normalized Hilbert--Schmidt distance at most
\(2\). The finite corner still costs \(o(1)\), so (5) gives
\[
 \limsup_n A_{\mathrm{cong}}(\pi_n)\leq2\sqrt r.           \tag{7}
\]
Together with (RCL1), this is \(r\geq\varepsilon^2/4\), proving (RCL3).

## 3. Central sign

For the \(\operatorname{SL}_2\) packet, the common image of \(-I\) is a
central involution. Its two spectral projections split (1) into exact sign
sectors. The finite-center version of Peterson--Thom rigidity says that an
extremal character is finite-quotient or is supported on the center with a
fixed central character. Applying the preceding argument in each sign
sector leaves only those regular central-character corners. Projectivizing
identifies them with the single \(\delta_e\) obstruction above.

No step selects coordinatewise lifts of the regular corner. Such a selection
is precisely the open flexible regular-branch liftability theorem.
