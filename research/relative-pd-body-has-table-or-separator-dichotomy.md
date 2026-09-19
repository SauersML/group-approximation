---
rg: 2
id: relative-pd-body-has-table-or-separator-dichotomy
kind: claim
title: The relative positive-definite body has an exact table-or-separator dichotomy
artifacts:
  - research/metric-projection-and-tfd-convert-table-distance-to-capture.md
distinct_from:
  finite-positive-definite-window-is-a-relative-corner-selector: that proves one positive-definite table is sufficient; this metrizes the entire table body, derives a uniform capture modulus, and gives the exact dual separator when no table is close.
  authenticated-core-union-basin-is-relative-liftability: that identifies the global moving-coordinate lift; this gives a finite-dimensional convex alternative at every coordinate without asserting that the separating branch is impossible.
  bounded-moments-cannot-recover-plancherel-grouping-score: that rules out fixed scalar windows; this identifies the stronger moving operator-valued witness which necessarily survives when capture fails.
---

Let \(\beta:B\to U(d)\) be an authenticated finite Iwahori-core
representation, let \(G=A_N\) be its forced finite quotient, and let
\(S\subset G\) be the fixed marked endpoint generating set. Define the
compact convex relative coefficient body
\[
 \mathcal C(G,B,\beta)=
 \left\{(F(s))_{s\in S}:
 \begin{array}{l}
 F(e)=1,\ [F(g^{-1}h)]_{g,h\in G}\succeq0,\\
 F(b)=\beta(b)\quad(b\in B)
 \end{array}\right\}.                                    \tag{TPD1}
\]
For a prescribed unitary marked tuple \(U=(U_s)_{s\in S}\), put
\[
 \Delta(U)^2=
 \inf_{C\in\mathcal C(G,B,\beta)}
 \frac1{|S|}\sum_{s\in S}\|U_s-C_s\|_{2,d}^2.            \tag{TPD2}
\]

There is a constant \(C_A<\infty\), depending only on the fixed marked
presentation and a property-\((T;FD)\) Kazhdan pair for \(A\), such that
\[
 D(U)\leq C_A\sqrt{\Delta(U)}.                            \tag{TPD3}
\]
The constant is independent of \(G,N,d,\beta\), and the minimizing table.
Thus \(\Delta(U_n)\to0\) produces exact congruence endpoints on
\(d_n+o(d_n)\) dimensions.

The alternative has an exact dual witness. If \(C^\star\) is the metric
projection of \(U\) onto \(\mathcal C(G,B,\beta)\) in the real
Hilbert--Schmidt direct sum and \(\Delta(U)>0\), then
\[
 Z=\frac{U-C^\star}{\Delta(U)}
\]
has norm one and satisfies
\[
 \langle Z,U\rangle-
 \sup_{C\in\mathcal C(G,B,\beta)}\langle Z,C\rangle
 \geq\Delta(U).                                          \tag{TPD4}
\]
Here the inner product is the real normalized Hilbert--Schmidt average over
\(S\).

Consequently every sequence with
\[
 \liminf_nD(U_n)\geq\varepsilon>0
\]
has, after discarding finitely many terms, moving norm-one operator
separators \(Z_n\) with a fixed positive margin
\[
 \langle Z_n,U_n\rangle-
 \sup_{C\in\mathcal C(G_n,B_n,\beta_n)}
 \langle Z_n,C\rangle
 \geq c_A\varepsilon^2.                                  \tag{TPD5}
\]
This is the requested compactness dichotomy: an almost-full finite quotient
table emerges, or a uniform noncongruence separation witness remains.

The separator is operator-valued and its quotient coordinates may grow.
By **bounded-moments-cannot-recover-plancherel-grouping-score**, it cannot
in general be replaced by one fixed bounded scalar word window. Proving
that the concrete Iwahori relators exclude the moving witnesses in (TPD5),
or constructing one compatible with vanishing defect, is precisely the
remaining arithmetic problem. The root remains open.

DERIVATION
metric-projection-and-tfd-convert-table-distance-to-capture
