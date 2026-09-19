---
rg: 2
id: plancherel-score-recovers-reducible-endpoint-grouping
kind: claim
title: A global Plancherel score exactly recovers regular endpoint grouping
artifacts:
  - research/tfd-mixed-intertwiner-stabilizes-global-multiplicity-score.md
distinct_from:
  central-projectors-overcount-regular-endpoint-payload: that shows irreducible blockwise refinement creates false residual width; this uses the full multiplicity vector at once and exactly regroups those blocks into regular endpoints.
  endpoint-expander-authenticates-bounded-residual-width: that authenticates a supplied irreducible tensor factor from commutators; this treats a reducible endpoint intrinsically through its global representation-ring multiplicities.
  finite-positive-definite-window-is-a-relative-corner-selector: that asks for a complete positive multiplication window producing an exact coordinate lift; this gives a dimension-free grouping criterion after such a finite quotient lift has been authenticated.
---

Let \(G\) be a finite quotient of
\(A=\operatorname{PSL}_2(\mathbb Z[1/2])\), and let
\[
 \beta\cong\bigoplus_{\rho\in\widehat G}m_\rho\rho,
 \qquad d=\sum_\rho m_\rho d_\rho                       \tag{PSG1}
\]
be an exact \(d\)-dimensional representation. Define its global regular
regrouping score by
\[
 \mathfrak R_G(\beta)=
 \min_{k\in\mathbb N_0}
 \frac1d\sum_{\rho\in\widehat G}
 d_\rho\,|m_\rho-kd_\rho|.                              \tag{PSG2}
\]
This uses the whole fusion/multiplicity vector, not one central block at a
time.

For a minimizing \(k\), the numerator in (PSG2) is exactly the total
unmatched physical dimension between \(\beta\) and \(k\lambda_G\). In
particular, if
\[
 \mathfrak R_G(\beta)=\zeta,                             \tag{PSG3}
\]
then \(\beta\) and \(k\lambda_G\) have a common exact subrepresentation
whose complements have total dimension \(\zeta d\), and
\[
 \bigl|\dim(k\lambda_G)-d\bigr|\leq\zeta d.              \tag{PSG4}
\]
Thus \(\zeta=o(1)\) is a dimension-free intrinsic certificate that the
entire reducible block is, after \(o(d)\) deletion/padding, one regular
congruence endpoint rather than an unbounded residual payload. In the
generalized Hilbert--Schmidt metric the corresponding endpoint distance is
at most \(2\sqrt{\zeta}\).

The score is uniformly stable among exact congruence lifts. Fix a
property-\((T;FD)\) Kazhdan set \(Q\) for \(A\). There is
\(C_Q<\infty\), independent of \(G,d\), and all multiplicities, such that
for two exact \(d\)-dimensional representations \(\beta,\gamma\) through
the same \(G\),
\[
 \left|\mathfrak R_G(\beta)-\mathfrak R_G(\gamma)\right|
 \leq C_Q
 \sum_{s\in Q}\|\beta(s)-\gamma(s)\|_{2,d}^2.            \tag{PSG5}
\]
Hence a complete quotient multiplication table which is close in
Hilbert--Schmidt norm to an exact lift cannot lose or invent a
positive-density regular grouping.

Fusion gives the same recognition principle:
\[
 \sigma\otimes\lambda_G\cong d_\sigma\lambda_G           \tag{PSG6}
\]
for every \(\sigma\in\widehat G\), so the Plancherel multiplicity vector
\((d_\rho)_\rho\) is the regular common eigenvector of all fusion matrices.
Formula (PSG2) is its physical weighted \(L^1\) distance.

This resolves the repeated-irrep ambiguity once a finite quotient
representation and its full multiplicity vector have been authenticated.
It does not recover either object from the raw Iwahori pair. Bounded word
moments and blockwise central expectations do not supply the required
moving quotient multiplication table; that relative coordinate-lift
problem remains open.

DERIVATION
tfd-mixed-intertwiner-stabilizes-global-multiplicity-score
