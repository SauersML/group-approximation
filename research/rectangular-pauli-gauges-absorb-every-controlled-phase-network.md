---
rg: 2
id: rectangular-pauli-gauges-absorb-every-controlled-phase-network
kind: claim
title: Rectangular Pauli gauges absorb every shared controlled-phase network
artifacts:
  - research/global-controlled-phase-ledger-and-finite-pauli-absorber-proof.md
distinct_from:
  controlled-pauli-commutator-robustly-measures-projection-overlap: that identity detects overlap once the controlled operators are gauge-free; this theorem constructs a simultaneous finite gauge cancellation for an arbitrary number of controlled cells.
  clifford-commutator-rank-is-packet-dimension: that computes the sector algebra of an abstract rectangular commutator matrix; this applies the matrix to a full controlled-gate network and proves that every visible Boolean profile extends.
  extraspecial-fusion-filter-is-local-and-normalizer-globalization-is-matricial: that builds additive Fourier one-hot projections and isolates nonnormal corner leakage; this closes only the phase-bicharacter attempt to lock the external gauges and leaves that nonnormal leakage route open.
---

**EXACT FINITE ABSORBER; NONMULTIPLICATIVE CORNER RETURNS REMAIN OPEN.**

Let \(I=\{1,\ldots,r\}\), let \(L=\{1,\ldots,s\}\), and fix an
arbitrary binary matrix \(b=(b_{ij})\in {\mathbf F}_2^{r\times s}\).
Consider one scalar visible profile

\[
 x=(x_i)\in{\mathbf F}_2^r,\qquad
 y=(y_j)\in{\mathbf F}_2^s.                              \tag{RPA1}
\]

A rectangular phase-only controlled network asks for a central involution
\(J=-I\), controller reflections \(X_0,Z_0\), and reflection families
\(U_i,V_j\) satisfying

\[
 [X_0,Z_0]_g=J,                                          \tag{RPA2}
\]

\[
 U_iZ_0U_i^{-1}=J^{x_i}Z_0,\qquad
 V_jX_0V_j^{-1}=J^{y_j}X_0,                              \tag{RPA3}
\]

\[
 [U_i,U_k]_g=[V_j,V_\ell]_g=1,\qquad
 [U_i,V_j]_g=J^{b_{ij}}.                                 \tag{RPA4}
\]

Here \([a,b]_g=aba^{-1}b^{-1}\). For **every** \(x,y,b\), all these
relations have an exact finite-dimensional representation, of dimension at
most \(2^{r+1}\).

Indeed, put

\[
 m_{ij}=x_iy_j+b_{ij}\pmod 2.                            \tag{RPA5}
\]

On one controller qubit and \(r\) gauge qubits, let \(X^{(k)},Z^{(k)}\)
denote the Pauli reflections on qubit \(k\), and set

\[
 U_i=(X^{(0)})^{x_i}Z^{(i)},\qquad
 V_j=(Z^{(0)})^{y_j}\prod_{i=1}^r(X^{(i)})^{m_{ij}},
 \qquad J=-I.                                            \tag{RPA6}
\]

Then (RPA2)--(RPA4) hold exactly.

Consequently, sharing all controlled cells globally does not lock their
multiplicity gauges when the extra relations see only a rectangular ledger
of central commutator phases. Every visible Boolean assignment, including a
forbidden assignment that the controlled commutator was meant to detect,
has a finite Pauli absorber obtained by changing the matrix \(m\).

This rules out a precise class of finite fusion-filter repairs: after an
isotypic selection, if the proposed lock reduces to two internally
commuting gauge families and prescribed root-of-unity commutator phases,
the phases can carry the missing overlap and the selector is not decoded.

The scope is essential. The theorem does not cover a nonnormal
\(q\)-compression, a relation with controlled off-corner leakage, a
noncentral return word, or a pointed trace condition not determined by the
commutator bicharacter. At least one such genuinely nonmultiplicative datum
is mandatory for the surviving corner route. No nonhyperlinear group is
claimed here.

DERIVATION
global-controlled-phase-ledger-and-finite-pauli-absorber-proof
