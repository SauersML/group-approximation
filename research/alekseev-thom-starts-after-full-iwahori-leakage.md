---
rg: 2
id: alekseev-thom-starts-after-full-iwahori-leakage
kind: claim
title: Alekseev-Thom Ulam stability starts after the full Iwahori leakage gate
artifacts:
  - research/stinespring-leakage-and-word-fillings-audit-ulam-input.md
distinct_from:
  multi-kraus-frame-energy-is-the-full-relative-pd-gate: that metrizes marked relative positive-definite feasibility by arbitrary Kraus frames; this audits the strictly stronger uniform unit-ball input of a matrix-algebra Ulam theorem.
  relative-table-separator-is-cayley-cocycle-obstruction: that transports the moving separator through marked Cayley rows; this explains why a theorem about all contractions cannot itself produce those missing rows.
  induced-rounding-needs-rms-section-fillings: that identifies growing section fillings for one induced construction; this gives the general word-area loss before any finite-presentation tuple can invoke matrix-algebra Ulam stability.
---

Alekseev--Thom, *The hyperfinite II1-factor is Ulam stable*,
arXiv:2606.07369v1 (submitted 5 June 2026), Definition 2.1 and Theorem 3.5,
do not turn finitely many presentation-relator defects into a repaired
matrix representation.

Their dimension-free matrix theorem starts with one map
\[
 \varphi:M_n(\mathbb C)_{\leq1}\longrightarrow M_{\leq1} \tag{ATF1}
\]
which, uniformly over the entire operator-norm unit ball, is
\(\varepsilon\)-additive, \(\varepsilon\)-homogeneous for every scalar of
modulus at most one, \(\varepsilon\)-multiplicative,
\(\varepsilon\)-star-preserving, and \(\varepsilon\)-unital. It concludes
that, in a semifinite amplification, \(\varphi\) is uniformly
\(\omega(\varepsilon)\)-close to a genuine unital star-homomorphism, where
\(\omega(\varepsilon)\to0\) independently of \(n\).

For a Stinespring compression
\[
 \varphi(x)=V^*\pi(x)V,\qquad P=VV^*,                    \tag{ATF2}
\]
the exact multiplicativity identity is
\[
 \varphi(xy)-\varphi(x)\varphi(y)
 =V^*\pi(x)(1-P)\pi(y)V.                                \tag{ATF3}
\]
Thus a uniform off-corner estimate
\[
 \sup_{\|y\|\leq1}\|(1-P)\pi(y)V\|_2\longrightarrow0     \tag{ATF4}
\]
does provide the multiplicativity hypothesis in (ATF1). But (ATF4) ranges
over every contraction of a full matrix algebra. The two Iwahori cubics
test only two marked group rows. No argument presently upgrades those two
tests to (ATF4).

The same gap is visible for a word-section compiler. If a tuple has
presentation-relator defect at most \(\delta\), and a multiplication cell
of a finite quotient has van Kampen area \(A(g,h)\), then its evaluated
basis-product defect is at most
\[
 A(g,h)\delta.                                           \tag{ATF5}
\]
For the naive linear extension, even assuming separately that it maps the
operator-norm unit ball to contractions, the elementary estimate is
\[
 \sup_{\|x\|,\|y\|\leq1}
 \|\Phi(xy)-\Phi(x)\Phi(y)\|_2
 \leq |G|\,A_{\max}\delta.                               \tag{ATF6}
\]
Neither \(|G|\) nor the filling parameter is bounded on the moving
Iwahori quotients. The required rate in (ATF6) is unavailable for an
arbitrary sequence with presentation defect merely tending to zero.

Consequently the Alekseev--Thom theorem is a valid terminal step under the
additional hypothesis of a dimension-free uniform unit-ball compiler. It
does not supply that compiler, and applying it directly to the two cubic
rows is circular. Small amplification is compatible with flexible
\(o(d)\)-padding once its hypothesis has been established.

This firewall does not say that such a compiler is impossible. It
identifies its exact missing estimate: a uniform all-contraction leakage
bound, stronger than the marked multi-Kraus energy gate (MKF4). No such
bound is proved here, and the root remains open.

DERIVATION
stinespring-leakage-and-word-fillings-audit-ulam-input
