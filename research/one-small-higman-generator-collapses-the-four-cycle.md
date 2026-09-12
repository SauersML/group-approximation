---
rg: 2
id: one-small-higman-generator-collapses-the-four-cycle
kind: claim
title: One Higman generator below the fifth-root radius collapses the whole cycle
artifacts:
  - research/one-small-higman-generator-collapses-the-four-cycle-proof.md
  - experiments/verify_cubic_spectral_basin.py
  - research/artifacts/non-mf-without-property-t.md
distinct_from:
  higman-four-cycle-intrinsic-mf-seed: that asks for collapse with no spectral assumption; this proves the collapse with an explicit dimension-free constant as soon as one generator is at operator-norm distance at most any fixed c below 2 sin(2 pi/5) from the identity, provided the relation defect is sufficiently small.
  periodic-higman-bs-clocks-have-three-opnorm-small-seams: that exhibits proper-subcycle clock packets whose conjugators have distance exactly 2 from the identity; this explains quantitatively why any full countermodel must remain outside the small-arc basin at every vertex.
---

**ESTABLISHED.**  Let `(U_0,U_1,U_2,U_3)` be finite-dimensional unitaries and
put

```text
delta=max_i ||U_i U_(i+1) U_i^* - U_(i+1)^2||_op,    (HAC1)
```

with indices modulo four.  If for some `j`

```text
||U_j-1||_op <= sqrt(2),                              (HAC2)
```

then

```text
max_i ||U_i-1||_op <= (15+8sqrt(2)) delta.            (HAC3)
```

In particular, along a microstate sequence whose maximum generator distance
is bounded away from zero, every generator eventually has distance strictly
greater than `sqrt(2)` from the identity. This wording is subsequence-sensitive:
inserting trivial coordinates is compatible with limsup separation.  Thus a countermodel to `higman-four-cycle-intrinsic-mf-seed`
cannot be made by keeping one occurrence in a logarithmic/small-spectrum
basin and placing the clock behavior only at the other three vertices: all
four occurrences must carry macroscopic circle spectrum simultaneously.


## Stronger spectral basin

Fix \(1/3\le a<2/5\), and put

\[
c_a=2\sin(\pi a),\quad
\delta_a=2\sin\left(\frac{\pi(2-5a)}{10}\right),\quad
N=2^{127}-1,
\]

\[
K=(24+12\pi)N+204\pi+4519.
\]

If one \(\|U_j-I\|\le c_a\) and the four-relator defect is less than
\(\delta_a\), then

\[
\max_i\|U_i-I\|\le K\delta.
\]

More generally, without a radius hypothesis, the auxiliary cubic estimate is

\[
\max_i\|U_i-I\|
\le 8(N+17)\|U_j^3-I\|+(24N+4519)\delta.
\]

Consequently every generator in any nontrivial homomorphism from Higman's
group into the unitary group of a matrix norm corona has distance at least
\(2\sin(2\pi/5)\) from the identity.

The proof combines the two-unitary cubic spectral theorem with fixed-power
propagation around the cycle. The large-spectrum case remains open, so this
claim does not establish `higman-four-cycle-intrinsic-mf-seed` or unconditional
existence of a non-MF group by a property-T-free proof.
