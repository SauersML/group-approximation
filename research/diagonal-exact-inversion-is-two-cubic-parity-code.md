---
rg: 2
id: diagonal-exact-inversion-is-two-cubic-parity-code
kind: claim
title: Diagonal exact-inversion gauges are a constrained two-cubic parity code
distinct_from:
  exact-inversion-transfer-is-twisted-coboundary: that gives the noncommutative coboundary Laplacian for every exact-inversion gauge; this identifies the diagonal gauge sector with an explicit binary code.
  proper-torus-reynolds-is-edge-refinement: that proves divergence for a real infinity-norm Green operator on a signed Reynolds sector; this gives the exact mod-two syndrome and Hamming correction problem, without transferring that real obstruction to binary decoding.
  right-regular-multiflips-have-exact-cubic-hole-charge: that treats operators in the right group algebra; diagonal multiplication gauges lie in a different maximal abelian algebra and exact inversion imposes split-normalizer orbit constraints.
---

Let \(Q\) be a finite quotient in which the two elements
\[
 a=xt,\qquad b=xt^2r
\]
have order three, and let \(X_0=\lambda_Q(x)\), \(R=\lambda_Q(r)\),
and \(T=\lambda_Q(t)\) on \(\ell^2(Q)\). Put
\[
 N=\langle r,x\rangle.
\]
For a function \(c:Q\to{\mathbb F}_2\), let
\[
 C_c=M_{(-1)^c},\qquad X_c=C_cX_0.                     \tag{DPC1}
\]

The involution and inversion rows
\[
 X_c^2=1,\qquad X_cRX_c=R^{-1}
\]
hold whenever \(c\) is constant on the left \(N\)-orbits. On the space
\[
 V_N=\{c\in{\mathbb F}_2^Q:c(ng)=c(g)\ 
       \hbox{ for all }n\in N,\ g\in Q\},              \tag{DPC2}
\]
define the two parity syndromes
\[
 h_a(c)(\langle a\rangle g)
 =c(g)+c(a^{-1}g)+c(a^{-2}g),
\]
\[
 h_b(c)(\langle b\rangle g)
 =c(g)+c(b^{-1}g)+c(b^{-2}g).                          \tag{DPC3}
\]
The sums are in \({\mathbb F}_2\) and are independent of the coset
representative. Then
\[
 \|(X_cT)^3-1\|_2^2
 =\frac{12}{|Q|}\,|\operatorname{supp}h_a(c)|,
\]
\[
 \|(X_cT^2R)^3-1\|_2^2
 =\frac{12}{|Q|}\,|\operatorname{supp}h_b(c)|.          \tag{DPC4}
\]

Consequently the exact diagonal endpoints over the retained core are
precisely the binary code
\[
 {\cal C}_N
 =V_N\cap\ker h_a\cap\ker h_b.                         \tag{DPC5}
\]
Moreover the optimal diagonal endpoint correction has the exact Hamming
formula
\[
 \inf_{c'\in{\cal C}_N}\|X_c-X_{c'}\|_2
 =2\sqrt{\operatorname{dist}_Q(c,{\cal C}_N)},          \tag{DPC6}
\]
where
\[
 \operatorname{dist}_Q(c,{\cal C}_N)
 =\frac1{|Q|}\min_{c'\in{\cal C}_N}
   |\{g:c(g)\ne c'(g)\}|.
\]

Without the constraint \(V_N\), (DPC3) is exactly the mod-two incidence
boundary of the 3-regular bipartite graph
\[
 E=Q,\qquad
 V=\langle a\rangle\backslash Q\ \sqcup\
   \langle b\rangle\backslash Q.                       \tag{DPC7}
\]
Thus unrestricted correction is a minimum \(T\)-join problem. The
constraint \(V_N\), however, identifies edge bits along left \(N\)-orbits,
and left \(N\)-translation need not preserve the two vertex partitions.
It is therefore not the cycle code of a quotient graph and an
unrestricted \(T\)-join cannot simply be averaged into \(V_N\).

A dimension-free decoder
\[
 \operatorname{dist}_Q(c,{\cal C}_N)
 \leq\omega\!\left(
 \frac{|\operatorname{supp}h_a(c)|
       +|\operatorname{supp}h_b(c)|}{|Q|}\right),
 \qquad \omega(s)\longrightarrow0,                     \tag{DPC8}
\]
would produce exact finite relative lifts for every diagonal
exact-inversion microstate. Conversely, a failure of (DPC8) would refute
this diagonal correction mechanism, but would not rule out a nondiagonal
Kraus selector. Neither alternative is proved here; the general root
remains open.

DERIVATION
diagonal-two-cubic-parity-code-proof
