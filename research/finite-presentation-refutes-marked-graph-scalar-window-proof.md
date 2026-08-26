---
rg: 2
id: finite-presentation-refutes-marked-graph-scalar-window-proof
kind: route
title: Put every actor relator in one table and project Clifford curvature to the finite symplectic quotient
target: finite-presentation-refutes-marked-graph-scalar-window
requires: []
---

Choose the Kun--Thom Theorem E pair at `r >= d+4`.  Allcock's finite
pre-Steinberg presentation together with his spherical identification
`PSt_r(R)=St_r(R)`, Suslin--Tulenbaev stability, and the regular-ring
Bass--Heller--Swan calculation `(FPS2)` show that `EL_r(R)`, hence
`G=EL_r(R) semidirect SL_d(Z)`, is finitely presented.

Put all presentation-relator prefixes, inverse triangles, finite generators
of `Gamma`, and a word for the marked `h` into one actor table.  A
scalar-only Clifford curvature has trivial image in `Sp(K)`, so the projected
actor maps satisfy every defining relator and extend to a homomorphism
`q:G->Sp(K)`.  This is a finite quotient.  Relative finite-quotient
blindness gives `q(h) in q(Gamma)`.

The tested covariance equations make the base lamp label `v_o` fixed by
`q(Gamma)` and send it by `q(h)` to the marked-neighbour label `v_(h o)`.
Hence the two labels coincide.  This contradicts their prescribed symplectic
pairing `b(v_o,v_(h o))=1`.  Therefore the proposed scalar-only section
fails on this single finite table.
