---
rg: 2
id: bcv-effective-microstate-search-nonhyperlinear-route
kind: route
title: Search the canonical microstate promised by hyperlinearity and feed its code to the BCV exactifier
target: non-hyperlinear-group
requires:
  - decidable-word-problem-hyperlinear-has-computable-canonical-microstate-modulus
  - bcv-universal-halt-canonical-microstate-exactification
  - bcv-no-computable-perfect-halt-readable-bound
---

Take the fixed finitely presented group \(\Gamma\), its word-problem decider
\(W\), and the total computable data \(n,q,A\) from the exactification
prerequisite.

Assume for contradiction that \(\Gamma\) is hyperlinear. Run the rational
Cayley search of the first prerequisite at the computable input

\[
 (n(M),q(M)).
\]

It halts with a coded rational canonical microstate \(U_M\). Define

\[
 B(M)=A(M,\ulcorner U_M\urcorner).                        \tag{BER1}
\]

Every operation in \((\mathrm{BER1})\) is total: \(n,q,A\) are total,
the word-problem decider is supplied, and hyperlinearity makes the
microstate search terminate. Hence \(B\) is a total computable function on
all machine descriptions, including nonhalting ones.

If \(M\) halts, the exactification prerequisite applied to \(U_M\) supplies
an attained-perfect finite-dimensional BCV ZPC strategy \(S_M\) with

\[
 \dim D_\infty(S_M)\le B(M).                              \tag{BER2}
\]

This is exactly the bound ruled out by
bcv-no-computable-perfect-halt-readable-bound. Therefore \(\Gamma\) is not
hyperlinear.

Notice what is doing the work: not the growth of approximate microstate
dimensions by itself, but the total finite-tolerance transfer
\((\mathrm{BER2})\) to an **exact** strategy. Dimensionwise compactness or
an asymptotic decoder cannot be substituted, because then
\((\mathrm{BER1})\) need not bound any exact strategy.
