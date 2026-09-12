---
rg: 2
id: proper-torus-incomplete-cover-curl-proof
kind: route
title: Build the split-torus gain graph and attach the two selected triangle orbits
target: proper-torus-diagonal-code-is-incomplete-cover-curl
requires:
  - diagonal-exact-inversion-is-two-cubic-parity-code
  - proper-torus-reynolds-is-edge-refinement
  - full-torus-diagonal-parity-has-linear-decoder
---

The subgroup \(H\) normalizes \(U\), so \(P=UH\) is a subgroup.
Likewise \(xHx=H\), so \(N=\langle H,x\rangle\) is the unoriented-edge
stabilizer. If \(Ng=Nh g\) with \(h\in H\), both cosets in (IGC2) are
unchanged because \(H<P\) and \(xHx=H\). Replacing \(g\) by \(xg\)
interchanges the two endpoints. Thus (IGC2) is well defined.

The same construction with \(H\) replaced by \(T_s\) gives the complete
graph on
\[
 \overline P\backslash G\cong\mathbb P^1(\mathbb F_p).
\]
Both subgroup indices
\[
 [\overline P:P]=[T_s:H]=i,\qquad
 [\overline N:N]=[T_s:H]=i
\]
equal \(i\). Edges incident to \(Pg\) are parametrized by \(H\backslash P\),
which has \(p\) elements, exactly the degree of the corresponding vertex
of \(K_{p+1}\). The induced map is therefore locally bijective and proves
(IGC3)--(IGC4). It is connected because \(P\) contains \(t\) and
\(\langle t,x\rangle=G\).

Here is a uniform check of the triangle assertion. Let \(y\in P\) and
\(q=xy\) have order three. Consider the three edges represented by
\[
 g,\qquad qg,\qquad q^2g.
\]
The edge of \(g\) has endpoints \(Pg,Pxg\). The edge of \(qg\) has one
endpoint
\[
 Pxqg=Py g=Pg.
\]
Since \(q^2=q^{-1}=y^{-1}x\), the edge of \(q^2g\) has one endpoint
\(Pq^2g=Pxg\). Finally the relation \(q^3=1\) gives
\[
 xy^{-1}x=yxy,
\]
so its other endpoint satisfies
\[
 Pxq^2g=Pxy^{-1}xg=Pyxyg=Pxyg=Pqg.
\]
The three edges therefore form a 3-cycle. Apply this first to \(y=t\)
and then to \(y=t^2r\). Since a left order-three orbit can be listed using
\(q\), \(q^{-1}\), or \(q^{-2}\), these are exactly the edge triples in
the two syndrome rows (DPC3).

For an edge cochain \(c\), cellular coboundary on one of these 2-cells is
the sum of its three boundary labels. Over \(\mathbb F_2\) no orientation
sign remains, proving (IGC5). Equations (IGC6)--(IGC8) are then the
definitions of cocycles, coboundaries, and first cellular cohomology.

Finally, replacing \(H\) by \(T_s\) changes neither row set
\(\langle a\rangle\backslash G\) nor
\(\langle b\rangle\backslash G\). The graph map has degree \(i\), but the
map on selected 2-cells has degree one. A simplicial \(i\)-sheeted cover
would instead contain \(i\) lifts of every base triangle. This proves the
incomplete-cover assertion and identifies (IGC9) with the diagonal
Hamming-decoding problem.
