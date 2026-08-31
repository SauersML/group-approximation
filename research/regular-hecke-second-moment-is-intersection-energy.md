---
rg: 2
id: regular-hecke-second-moment-is-intersection-energy
kind: claim
title: The regular Hecke second moment is intersection energy
distinct_from:
  hecke-rank-controls-coverage-but-has-half-space-ceiling: that uses only the zero first supertrace to give a one-half rank ceiling; this computes the exact second moment and gives the much smaller Iwahori intersection ceiling.
  hecke-top-spectrum-coverage-controls-window: that detects a unital operator frame in the near-top space; this shows why that space can have vanishing normalized dimension even at a perfect endpoint.
  regular-core-window-is-a-hecke-kraus-hull: that defines the transfer selector; this traces its square through the core double coset.
---

Let \(G\) be finite, \(B<G\), \(x=x^{-1}\notin B\), and use the regular
finite-core transfer

\[
D=(\lambda_G(B))',\qquad
X_0=\lambda_G(x),\qquad
T_X(A)=E_D(X_0AX)
\]

for an arbitrary selfadjoint unitary \(X\). Put

\[
I=B\cap xBx,\qquad \alpha(c)=xcx\quad(c\in I).
\]

Then the normalized second supertrace has the exact formula

\[
\frac{\operatorname{Tr}_{L^2(D)}(T_X^2)}
     {\dim_{\mathbb C}D}
 =
 \frac1{|B|}\sum_{c\in I}
 \operatorname{Re}\tau\!\left(
 X\lambda(c^{-1})X\lambda(\alpha(c))\right).           \tag{HMI1}
\]

Equivalently,

\[
\frac{\operatorname{Tr}(T_X^2)}{\dim_{\mathbb C}D}
 =
 \frac{|I|}{|B|}
 -\frac1{2|B|}\sum_{c\in I}
 \left\|X\lambda(c^{-1})X\lambda(\alpha(c))-1\right\|_2^2.             \tag{HMI2}
\]

Thus

\[
0\leq
\frac{\operatorname{Tr}(T_X^2)}{\dim_{\mathbb C}D}
\leq\frac{|B\cap xBx|}{|B|}.                          \tag{HMI3}
\]

The upper bound is attained exactly when \(X\) implements the canonical
\(x\)-conjugation on the whole intersection subgroup.

Consequently, if

\[
Q_\epsilon=1_{[1-\epsilon,1]}(T_X),\qquad 0\leq\epsilon<1,
\]

then

\[
\frac{\operatorname{rank}(Q_\epsilon)}
     {\dim_{\mathbb C}D}
\leq
\frac{|B\cap xBx|}
     {|B|(1-\epsilon)^2}.                              \tag{HMI4}
\]

For the standard prime Iwahori pair in
\(G=\operatorname{PSL}_2(\mathbb F_p)\), the intersection is the split
diagonal torus and has index \(p\) in \(B\). Hence

\[
\frac{\operatorname{rank}(Q_\epsilon)}
     {\dim_{\mathbb C}D}
\leq\frac1{p(1-\epsilon)^2}.                           \tag{HMI5}
\]

If the inversion row \(X\lambda(r)X=\lambda(r^{-1})\) is exact and \(r\)
generates that torus, then (HMI2) is an equality with second moment \(1/p\).

This explains the module-position frontier sharply. At exact regular
endpoints the top intertwiner space contains a unital frame and the
relative coverage is one, while its normalized spectral dimension is
already of order \(1/p\). Neither first-moment concentration nor
second-moment bulk can produce the corner. The required arithmetic theorem
must prove that this vanishing-density module contains an almost-unital
operator frame. The nonhyperlinear-group root remains open.

DERIVATION
regular-hecke-intersection-energy-proof
