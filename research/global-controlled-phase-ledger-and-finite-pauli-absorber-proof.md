---
rg: 2
id: global-controlled-phase-ledger-and-finite-pauli-absorber-proof
kind: route
title: Build the simultaneous Pauli absorber for a rectangular controlled-phase ledger
target: rectangular-pauli-gauges-absorb-every-controlled-phase-network
requires:
  - controlled-pauli-commutator-robustly-measures-projection-overlap
  - clifford-commutator-rank-is-packet-dimension
  - extraspecial-fusion-filter-is-local-and-normalizer-globalization-is-matricial
---

# Build the simultaneous Pauli absorber for a rectangular controlled-phase ledger

## 1. The finite Pauli carrier

Fix finite sets \(I=\{1,\ldots,r\}\) and
\(L=\{1,\ldots,s\}\), visible bits \(x_i,y_j\), and prescribed cross
phases \(b_{ij}\), all over \({\mathbf F}_2\). Define

\[
 m_{ij}=x_iy_j+b_{ij}.                                  \tag{1}
\]

Use the Hilbert space

\[
 {\cal H}={\mathbf C}^2\otimes({\mathbf C}^2)^{\otimes r}.\tag{2}
\]

The first tensor factor is the controller qubit. Label the remaining
factors by \(i\in I\). Write \(X^{(k)},Z^{(k)}\) for the usual Pauli
reflections on factor \(k\), extended by the identity on every other
factor. Thus

\[
 [X^{(k)},Z^{(k)}]_g=-I,\qquad
 [X^{(k)},Z^{(\ell)}]_g=1\quad(k\ne\ell).                \tag{3}
\]

Put

\[
 J=-I,\qquad X_0=X^{(0)},\qquad Z_0=Z^{(0)},             \tag{4}
\]

and introduce the gauge reflections

\[
 A_i=Z^{(i)},\qquad
 B_j=\prod_{k=1}^r(X^{(k)})^{m_{kj}}.                   \tag{5}
\]

All the \(A_i\) commute with one another, and all the \(B_j\) commute with
one another. Their rectangular commutator ledger is

\[
 [A_i,B_j]_g=J^{m_{ij}}.                                \tag{6}
\]

This is an explicit representation of the rectangular class-two
two-group. No stability or approximation theorem is being used.

## 2. Dress the visible controlled operators

Define

\[
 U_i=(X_0)^{x_i}A_i,\qquad
 V_j=(Z_0)^{y_j}B_j.                                    \tag{7}
\]

Controller and gauge factors act on different tensor coordinates.
Consequently every \(U_i,V_j\) is a self-adjoint involution.

The controller covariance is immediate:

\[
 \begin{aligned}
 U_iZ_0U_i^{-1}
   &=(X_0)^{x_i}Z_0(X_0)^{x_i}
     =J^{x_i}Z_0,\\
 V_jX_0V_j^{-1}
   &=(Z_0)^{y_j}X_0(Z_0)^{y_j}
     =J^{y_j}X_0.                                      \tag{8}
 \end{aligned}
\]

Because the controller powers within each family commute, equations (5)
and (7) also give

\[
 [U_i,U_k]_g=1,\qquad [V_j,V_\ell]_g=1.                 \tag{9}
\]

For the cross rows, the controller commutator and gauge commutator are
central and act on different tensor factors. Hence

\[
 \begin{aligned}
 [U_i,V_j]_g
  &=[(X_0)^{x_i},(Z_0)^{y_j}]_g[A_i,B_j]_g\\
  &=J^{x_iy_j}J^{m_{ij}}
    =J^{b_{ij}},                                       \tag{10}
 \end{aligned}
\]

where the last equality is (1). Equations (8)--(10) prove every required
relation. The dimension is \(2^{r+1}\).

One may reduce the number of gauge qubits to
\(\operatorname{rank}_{{\mathbf F}_2}(m)\) by independent row and column
operations, as in clifford-commutator-rank-is-packet-dimension. The larger
carrier (2) is preferable here because it makes simultaneous extension of
all cells completely explicit.

## 3. Why global sharing does not help at the phase level

A single gauge-free controlled Pauli cell has the exact overlap signal

\[
 \|[C_X(p),C_Z(q)]_g-I\|_2^2
 =4\|pq\|_2^2+2\|pq-qp\|_2^2.                           \tag{11}
\]

On a scalar visible atom \(p=x_i\), \(q=y_j\), the controller contributes
the phase \(J^{x_iy_j}\). An external multiplicity gauge can cancel that
phase. A tempting repair is to share the gauges among all cells and impose
all their pairwise commutators at once.

Equations (1)--(10) show that this does not work. The entire cancellation
table is one arbitrary rectangular binary matrix \(m\), and the Pauli
operators (5) realize every such matrix simultaneously. Adding more cells,
cycles in the bipartite incidence graph, or every possible cross phase row
does not create an obstruction: the same construction fills the complete
rectangle.

More formally, suppose a proposed compiler has scalar selector sectors
\(S_i=J^{x_i}\), \(T_j=J^{y_j}\), and its only rows involving the external
gauges, after fixing such a sector, are:

1. involutivity;
2. commutation inside the \(U\)-family and inside the \(V\)-family;
3. the two controller covariances in (8);
4. prescribed central cross phases as in (10).

Then every selector sector allowed by the remaining visible relations
extends to an exact finite-dimensional representation. In particular the
gauge rows cannot remove a losing visible atom.

## 4. Exact boundary for fusion and corner proposals

A finite isotypic or fusion filter can turn multiplicity operators into a
projective representation. If the only data returned by that projective
representation are the central commutator phases of two abelian gauge
families, its multiplier is exactly a rectangular bicharacter. The finite
Pauli carrier above absorbs it. Thus changing the size of the finite packet
or replacing private cells by a shared phase ledger does not authenticate
the controlled form.

This statement does not say that every finite-group corner is useless.
The additive Fourier projections in
extraspecial-fusion-filter-is-local-and-normalizer-globalization-is-matricial
already evade the literal-selector tensor obstruction. Their live seam is
nonnormal compression. For an isotypic projection \(q\),

\[
 (qgq)(qhq)-qghq=-qg(1-q)hq.                            \tag{12}
\]

The leakage term in (12) is not a commutator bicharacter and is absent from
the hypotheses above. Likewise, a noncentral return word, a fusion
associator that is not determined by pairwise phases, or a trace-selected
pointed face may escape the absorber.

Therefore the next viable decoder must make at least one such
nonmultiplicative quantity observable and must control it in normalized
Hilbert--Schmidt norm. A rectangular central-phase gauge lock, however
large and however globally shared, is closed by the exact finite model
(2)--(10). This is a no-go theorem for that compiler class, not a
nonhyperlinear-group construction.
