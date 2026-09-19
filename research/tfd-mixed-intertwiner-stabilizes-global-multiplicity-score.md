---
rg: 2
id: tfd-mixed-intertwiner-stabilizes-global-multiplicity-score
kind: route
title: Use a mixed TFD intertwiner to stabilize the global multiplicity score
target: plancherel-score-recovers-reducible-endpoint-grouping
requires:
  - tfd-low-leakage-compressions-flexibly-reduce
  - central-projectors-overcount-regular-endpoint-payload
---

# Weighted multiplicity distance is exactly unmatched rank

Fix \(k\geq0\). The multiplicity of \(\rho\) in \(k\lambda_G\) is
\(kd_\rho\). The maximal common subrepresentation of \(\beta\) and
\(k\lambda_G\) therefore has multiplicity
\[
 \min(m_\rho,kd_\rho)
\]
at \(\rho\). Put
\[
 A_k=\sum_\rho d_\rho(m_\rho-kd_\rho)_+,\qquad
 B_k=\sum_\rho d_\rho(kd_\rho-m_\rho)_+.                 \tag{1}
\]
These are exactly the dimensions left unmatched on the \(\beta\) and
\(k\lambda_G\) sides. Hence
\[
 A_k+B_k=\sum_\rho d_\rho|m_\rho-kd_\rho|,               \tag{2}
\]
while
\[
 \dim(k\lambda_G)-d=B_k-A_k.                             \tag{3}
\]
Minimizing (2), then dividing by \(d\), proves (PSG3)--(PSG4).

Identify the common subrepresentations unitarily. All generator matrices
agree exactly there. On complementary carriers, unitary matrices differ by
at most two in operator norm. The squared normalized Hilbert--Schmidt cost
is therefore at most four times the total unmatched rank fraction. This
gives the stated \(2\sqrt\zeta\) generalized-distance estimate. The same
argument shows conversely that every exact common-subrepresentation
matching bounds (PSG2) by its unmatched rank fraction.

# A mixed Kazhdan projection controls multiplicity transport

Let \(\beta,\gamma:G\to U(d)\) be exact and define the finite-dimensional
unitary representation of \(A\) on \(M_d\)
\[
 \Theta(g)T=\beta(g)T\gamma(g)^*.                        \tag{4}
\]
Its fixed space is
\[
 \operatorname{Hom}_G(\gamma,\beta).
\]
The identity matrix has displacement
\[
 \|\Theta(s)1-1\|_{2,d}
 =\|\beta(s)-\gamma(s)\|_{2,d}.                          \tag{5}
\]
Let \(P\) be the Hilbert--Schmidt orthogonal projection onto the fixed
space and put \(T=P(1)\). Property \((T;FD)\), applied to the orthogonal
complement of the fixed space, gives
\[
 \|1-T\|_{2,d}^2
 \leq\kappa^{-2}
 \sum_{s\in Q}\|\beta(s)-\gamma(s)\|_{2,d}^2.            \tag{6}
\]

Because \(T\) intertwines, \(T^*T\) lies in \(\gamma(G)'\) and \(TT^*\)
lies in \(\beta(G)'\). The polar part of \(T\) is therefore a partial
unitary intertwiner between exact subrepresentations. On \(\ker T\), the
operator \(1-T\) is the identity, so
\[
 \frac{\dim\ker T}{d}\leq\|1-T\|_{2,d}^2.                \tag{7}
\]
The initial and final supports of the polar part have the same rank. Thus
\(\beta\) and \(\gamma\) possess a common subrepresentation of dimension at
least
\[
 d\bigl(1-\|1-T\|_{2,d}^2\bigr).                         \tag{8}
\]

Write \(m_\rho,n_\rho\) for their multiplicities. Since both total
dimensions equal \(d\), maximal common rank gives
\[
 \frac1d\sum_\rho d_\rho|m_\rho-n_\rho|
 \leq2\|1-T\|_{2,d}^2.                                  \tag{9}
\]
For every \(k\), the reverse triangle inequality implies
\[
 \left|
 \sum_\rho d_\rho|m_\rho-kd_\rho|
 -
 \sum_\rho d_\rho|n_\rho-kd_\rho|
 \right|
 \leq\sum_\rho d_\rho|m_\rho-n_\rho|.                   \tag{10}
\]
Taking minima in \(k\), then using (6), (9), and (10), proves (PSG5) with
\(C_Q=2\kappa^{-2}\).

# Fusion recognizes the same global ray

The regular representation satisfies
\[
 \sigma\otimes\lambda_G\cong d_\sigma\lambda_G
\]
because its character is \(|G|\) at the identity and zero elsewhere.
Equating irreducible multiplicities is exactly the common fusion-eigenvector
identity (PSG6). Thus the global vector used in (PSG2) is intrinsic to the
full representation ring and regroups all repeated atoms at once.

The mixed-intertwiner argument proves uniform stability after an exact
finite quotient lift is available. It does not evaluate the quotient
matrices, central ranks, or fusion vector on the raw approximate Iwahori
pair. Constructing those moving coordinates is the remaining relative-lift
problem.
