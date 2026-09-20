---
rg: 2
id: triangle-edge-matching-one-edge-holonomy-proof
kind: route
title: Equalize edge eigenvalue counts with linear characters, align two edges by near-identity intertwiners, and feed the third edge to (HA)
target: triangle-edge-matching-reduces-to-one-edge-holonomy
requires:
  - triangle-of-finite-groups-hs-stability-is-edge-matching
  - hrf-cyclic-edge-quadratic-padding
---

All norms are normalized Hilbert--Schmidt norms. This route uses the complete
spectral transport and polar-intertwiner proof in
`research/artifacts/hyperbolic-rf-quadratic-edge-preprocessing-2026-09-20.md`.

## (EM) implies (HA)

The (HA) data already meet the (EM) hypotheses, with two edge errors zero.

## (HA) implies (EM)

Take genuine vertex representations in common dimension d_n whose three
edge errors are bounded by epsilon_n tending to zero. The quantitative
padding lemma produces genuine vertex representations rho_i' in dimension
D_n=d_n+m_n with m_n/d_n=O(epsilon_n²), the a and b edges exactly matched,
the c error O(epsilon_n), and changes O(epsilon_n) from the padded inputs
rho_i direct_sum S_i. Constants depend only on p.

Apply (HA) to this sequence. It gives genuine colimit representations pi_n
in dimensions L_n>=D_n, with L_n/D_n tending to one and compression errors
tending to zero on every vertex-group element. By the triangle inequality,
these compressions also approximate rho_i direct_sum S_i. Compress again
to the original d_n coordinates. The normalized HS error increases by at
most sqrt(D_n/d_n), which tends to one. Finally

    L_n/d_n = (L_n/D_n)(1+m_n/d_n) -> 1.

This is (EM). Its equivalence to flexible HS stability is the other listed
dependency. No claim that (HA) actually holds is used or proved here.

## Review

The quantitative lemma was independently checked by the hyperbolic
alternatives lane on 2026-09-20, including transport signs, polar kernel
completion, all error constants, and the normalization after compression.
