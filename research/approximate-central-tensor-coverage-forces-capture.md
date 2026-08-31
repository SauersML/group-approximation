---
rg: 2
id: approximate-central-tensor-coverage-forces-capture
kind: claim
title: Approximate central coverage by bounded tensor blocks forces global capture
artifacts:
  - research/round-finite-subgroup-corners-and-apply-block-capture.md
distinct_from:
  bounded-payload-congruence-tensors-have-uniform-capture: that assumes an exact common reducing tensor decomposition; this permits an approximately central carrier and quantifies the off-diagonal mass needed to authenticate it.
  iwahori-outlier-localization: that localizes low-energy operator spaces without producing a reducing physical carrier; this starts from a candidate physical carrier and proves that finite-subgroup spectral rounding creates no additional obstruction.
  raw-core-central-reynolds-authentication-is-circular: that fences central idempotents evaluated through an unauthenticated moving quotient; this gives the exact consequence once a candidate projection and its tensor-block interpretation have actually been produced.
---

Let \(\pi=(\pi_+,\pi_-)\) be an exact modular-vertex pair on
\(\mathbb C^d\), let \(p\) be a projection of normalized rank
\[
 q=\operatorname{tr}_d(p)=1-r,
\]
and use fixed order-two/order-three generators \(x,a\) in each vertex.
Define the physical off-diagonal mass
\[
 \Omega(p,\pi)=
 \max_{\epsilon\in\{+,-\},\,s\in\{x,a\}}
 \|[p,\pi_\epsilon(s)]\|_{2,d}.                          \tag{ACT1}
\]

Fix \(D\) and \(q_0>0\). If \(q\geq q_0\), the compressed generator tuples
on \(p\mathbb C^d\) can be changed by at most
\[
 C_{q_0}\Omega(p,\pi)                                    \tag{ACT2}
\]
in the original normalized Hilbert--Schmidt metric to exact
representations of both modular vertices. Suppose the resulting exact
corner pair is at corner-normalized distance at most \(\zeta\) from the
bounded-payload congruence tensor hull of payload size at most \(D\).
Then
\[
 D(\pi)\leq
 2\sqrt r+
 C_{D,q_0}
 \bigl(\operatorname{def}(\pi)+\Omega(p,\pi)+\zeta
 \bigr)^{\alpha_D},                                     \tag{ACT3}
\]
for constants \(C_{D,q_0}<\infty\) and \(\alpha_D>0\) independent of
dimension, congruence levels, tensor multiplicities, and the projection.

Consequently, if
\[
 \operatorname{def}(\pi_n)\to0,\qquad
 \liminf_nD(\pi_n)\geq\varepsilon>0,
\]
then for every fixed \(D\) no projections \(p_n\) can simultaneously satisfy
\[
 \liminf_n\operatorname{tr}(p_n)>1-\varepsilon^2/4,\quad
 \Omega(p_n,\pi_n)\to0,\quad \zeta_n\to0.                \tag{ACT4}
\]
Equivalently, every attempted finite-subgroup/central-idempotent
authentication faces the following sharp alternative:

1. at least \(\varepsilon^2/4\) of physical rank remains uncovered;
2. the proposed central carrier has nonvanishing off-diagonal mass; or
3. its authenticated corner stays away from every bounded-dimensional
   payload tensor stratum.

On the pure regular-character face, the third alternative is precisely an
unbounded irreducible-payload obstruction on positive physical rank.
Finite-subgroup spectral projection rounding itself is not a remaining
gate.

This theorem does not construct \(p\) or identify its tensor factors.
Producing an almost-central carrier with \(\zeta\to0\), or proving that none
can exist, is the surviving authentication problem. The root remains open.

DERIVATION
round-finite-subgroup-corners-and-apply-block-capture
