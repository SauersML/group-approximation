---
rg: 2
id: full-torus-diagonal-parity-has-linear-decoder
kind: claim
title: Full-torus diagonal parity has a dimension-free linear decoder
distinct_from:
  full-torus-reynolds-is-multipartite-curl: that identifies the real signed Reynolds column with triangle curl and bounds a linear Green problem; this proves a nonlinear mod-two Hamming decoder for diagonal involution gauges.
  diagonal-exact-inversion-is-two-cubic-parity-code: that reduces the general split-normalizer sector to a constrained binary code; this solves the code when the retained torus is the full projective split torus and both triangle classes occur.
  right-regular-multiflips-have-exact-cubic-hole-charge: that gives an exact Kraus coverage law for right-algebra flips; this constructs an actual nearby exact endpoint for diagonal multiplication flips.
---

Let \(Q=\operatorname{PSL}_2(\mathbb F_p)\), with \(p>3\). Assume that
\(\langle h(2)\rangle\) is the full projective split torus and that \(2\)
is nonsquare modulo \(p\). Use the square-free endpoint
\[
 X_0=\lambda_Q(x),\qquad R=\lambda_Q(r),\qquad
 T=\lambda_Q(t),
\]
where \(r=h(2)\), and let \(X_c=M_{(-1)^c}X_0\) be a diagonal gauge
satisfying the exact involution and inversion rows.

Write
\[
 \delta_a=\|(X_cT)^3-1\|_2,\qquad
 \delta_b=\|(X_cT^2R)^3-1\|_2.                         \tag{FTD1}
\]
Then there is a diagonal gauge \(X_{c'}\) over the same core for which
all four square-free extension rows are exact and
\[
 \operatorname{dist}_Q(c,c')
 \leq\frac{\delta_a^2+\delta_b^2}{8},                  \tag{FTD2}
\]
\[
 \|X_c-X_{c'}\|_2
 \leq\frac1{\sqrt2}\sqrt{\delta_a^2+\delta_b^2}.        \tag{FTD3}
\]
The constants are independent of \(p\).

More explicitly, put \(n=p+1\). The left cosets of the full split-torus
normalizer are the unordered pairs in
\(\mathbb P^1(\mathbb F_p)\), hence the edge set of \(K_n\). The two
cubic row orbits together test both cyclic orientations of every
geometric triangle. Modulo two, their common kernel is exactly the cut
code
\[
 c'(\{u,v\})=\phi(u)+\phi(v),\qquad
 \phi:\mathbb P^1(\mathbb F_p)\to\mathbb F_2.           \tag{FTD4}
\]

If \(B\) is the number of geometric triangles with odd edge parity, a
one-vertex anchor produces a cut differing from \(c\) on at most
\[
 \frac{3B}{n}
\]
edges. Since each bad geometric triangle occurs in two cyclic row
orbits,
\[
 \delta_a^2+\delta_b^2
 =8\,\frac{B}{\binom n3}.                              \tag{FTD5}
\]
After normalizing by \(\binom n2\), (FTD2) follows.

Thus a positive-density diagonal carrier cannot hide behind vanishing
cubic defects in the full-normalizer, two-triangle-class regime. The
arithmetic obstruction is confined to proper subtori or incomplete
triangle classes. In particular, this theorem does not solve the
proper-\(\langle h(2)\rangle\) square-free levels used by the remaining
authenticated-core problem, and the general root remains open.

DERIVATION
full-torus-diagonal-parity-decoder-proof
