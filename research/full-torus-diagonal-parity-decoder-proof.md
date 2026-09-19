---
rg: 2
id: full-torus-diagonal-parity-decoder-proof
kind: route
title: Decode triangle parity by anchoring one projective vertex
target: full-torus-diagonal-parity-has-linear-decoder
requires:
  - diagonal-exact-inversion-is-two-cubic-parity-code
  - full-torus-reynolds-is-multipartite-curl
---

Let \(N=\langle h(2),x\rangle\). Under the full-torus hypothesis, \(N\)
is the stabilizer of the unordered pair
\(\{\infty,0\}\) in \(Q\). Thus
\[
 N\backslash Q\ \longleftrightarrow\
 \binom{\mathbb P^1(\mathbb F_p)}2.                    \tag{FTP1}
\]
A left \(N\)-invariant bit function is therefore an edge labeling of
\(K_n\), where \(n=p+1\). Its normalized Hamming weight on \(Q\) is
exactly its normalized edge weight because every coset has size
\(|N|\).

The full-torus triangle-curl identification says that, when \(2\) is
nonsquare, the two cubic orbits together contain every cyclic triangle.
After removing the threefold repetition by each order-three stabilizer,
the number of rows is
\[
 2|Q|/3=2\binom n3.
\]
Hence each of the two cyclic orientations of every geometric triangle
occurs exactly once. Over \(\mathbb F_2\) orientation signs disappear, so
a geometric triangle is bad in exactly two rows. If \(B\) is the number
of bad geometric triangles, the exact residual formula (DPC4) gives
\[
 \delta_a^2+\delta_b^2
 =\frac{12}{|Q|}\,2B
 =8\,\frac{B}{\binom n3},                              \tag{FTP2}
\]
using \(|Q|=3\binom n3\).

It remains to decode the complete-graph triangle test. For a vertex
\(z\), set
\[
 \phi_z(z)=0,\qquad \phi_z(u)=c(\{z,u\})\quad(u\ne z),
\]
and define the cut
\[
 c_z'(\{u,v\})=\phi_z(u)+\phi_z(v).
\]
The cut agrees with \(c\) on every edge incident to \(z\). On an edge
\(\{u,v\}\) disjoint from \(z\), its discrepancy is
\[
 c(\{u,v\})+c(\{z,u\})+c(\{z,v\}),
\]
which is precisely the parity of the triangle \(\{z,u,v\}\). Therefore
\[
 |\operatorname{supp}(c-c_z')|
 =|\{\hbox{bad triangles containing }z\}|.             \tag{FTP3}
\]
Averaging (FTP3) over \(z\) counts every bad triangle three times, so
some anchor satisfies
\[
 |\operatorname{supp}(c-c_z')|\leq\frac{3B}{n}.         \tag{FTP4}
\]
Dividing by \(\binom n2\) and using
\[
 \frac{3\binom n3}{n\binom n2}=\frac{n-2}{n}\leq1
\]
shows
\[
 \operatorname{dist}_Q(c,c_z')
 \leq\frac{B}{\binom n3}
 =\frac{\delta_a^2+\delta_b^2}{8}.
\]
Every cut has zero parity on every triangle, so the diagonal parity-code
theorem makes \(X_{c_z'}\) an exact extension over the retained core.
Finally its exact Hamming-to-Hilbert--Schmidt identity gives
\[
 \|X_c-X_{c_z'}\|_2
 =2\sqrt{\operatorname{dist}_Q(c,c_z')},
\]
which proves (FTD3).
