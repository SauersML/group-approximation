---
rg: 2
id: diagonal-two-cubic-parity-code-proof
kind: route
title: Evaluate diagonal cubic holonomies and identify the constrained incidence boundary
target: diagonal-exact-inversion-is-two-cubic-parity-code
requires:
  - iwahori-square-free-bs14-presentation
  - exact-inversion-transfer-is-twisted-coboundary
  - proper-torus-reynolds-is-edge-refinement
---

Write \(s(g)=(-1)^{c(g)}\), so \(C_c=M_s\). Conjugation by a left
regular operator translates the diagonal function:
\[
 \lambda(q)M_s\lambda(q)^{-1}=M_{s(q^{-1}\,\cdot)}.     \tag{DPP1}
\]
Since \(C_c=C_c^{-1}\), the equality \(X_c^2=1\) is equivalent to
\[
 X_0C_cX_0=C_c,
\]
which by (DPP1) is exactly left \(x\)-invariance of \(c\). Under that
condition,
\[
 X_cRX_c=C_cR^{-1}C_c.
\]
This equals \(R^{-1}\) exactly when \(C_c\) commutes with \(R\), which by
(DPP1) is left \(r\)-invariance. The two rows are therefore equivalent to
\(c\in V_N\).

Now \(X_cT=C_c\lambda(a)\). Since \(a^3=1\),
\[
 (X_cT)^3
 =C_c\,\operatorname{Ad}_{\lambda(a)}(C_c)\,
       \operatorname{Ad}_{\lambda(a)}^2(C_c).           \tag{DPP2}
\]
Its diagonal value at \(g\) is
\[
 (-1)^{c(g)+c(a^{-1}g)+c(a^{-2}g)}
 =(-1)^{h_a(c)(\langle a\rangle g)}.                   \tag{DPP3}
\]
The parity in (DPP3) is constant on the three-element left
\(\langle a\rangle\)-orbit. On a good orbit the residual vanishes; on a
bad orbit it is \(-2\) at each of three coordinates. Normalized trace
therefore gives
\[
 \|(X_cT)^3-1\|_2^2
 =|Q|^{-1}\,|\operatorname{supp}h_a(c)|\cdot3\cdot4.
\]
Replacing \(a\) by \(b\) proves the second formula in (DPC4).
Together with the first two rows this proves (DPC5).

For two bit functions \(c,c'\), the diagonal signs differ by zero where
the bits agree and by magnitude two where they differ. Since right
multiplication by \(X_0\) preserves normalized Hilbert--Schmidt norm,
\[
 \|X_c-X_{c'}\|_2^2
 =\|C_c-C_{c'}\|_2^2
 =\frac4{|Q|}|\{g:c(g)\ne c'(g)\}|.
\]
Minimization over (DPC5) proves (DPC6).

Finally form the bipartite graph (DPC7), joining the edge \(g\) to
\(\langle a\rangle g\) and \(\langle b\rangle g\). Each vertex has three
incident edges because \(a\) and \(b\) have order three. The mod-two
incidence boundary of an edge function \(c\) is exactly
\((h_a(c),h_b(c))\). Hence its unrestricted kernel is the graph cycle
space and a correction with prescribed syndrome is a \(T\)-join.

The last observation does not remove the arithmetic constraint. A left
translate \(g\mapsto ng\) induces a graph automorphism only when it
respects both order-three coset partitions; a general
\(n\in\langle r,x\rangle\) need not normalize either
\(\langle a\rangle\) or \(\langle b\rangle\). Thus identifying the bits on
left \(N\)-orbits is not passage to a graph quotient. This is the same
missing-label geometry isolated by the proper-subtorus Reynolds
refinement, now stated exactly over \({\mathbb F}_2\). The real
infinity-norm Green divergence proved there neither proves nor refutes
the Hamming modulus (DPC8).
