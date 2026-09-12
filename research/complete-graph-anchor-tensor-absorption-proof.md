---
rg: 2
id: complete-graph-anchor-tensor-absorption-proof
kind: route
title: Split off one selfless coordinate and absorb the restricted direct sum
target: complete-graph-products-selfless-anchor
requires:
  - complete-selflessness-is-tensor-stable
  - complete-selflessness-tensor-permanence
  - cstar-simple-groups-products-directed-unions
  - robert-tracial-selfless-regularity
artifacts:
  - research/artifacts/stw91-complete-graph-anchor-audit-2026-08-30.md
---

Because Gamma is complete, graph-product normal form gives

    P = direct_sum_v G_v
      = G_(v_0) times H,

where H is the restricted direct sum of the other vertex groups. The regular
representation gives the canonical trace-preserving identification

    C*_r(P)
      = C*_r(G_(v_0)) tensor_min C*_r(H).

Suppose first that every G_v is C-star-simple. Finite direct products of the
groups away from v_0 are C-star-simple, and H is their directed union.
Therefore H is C-star-simple. Its reduced algebra is simple and its canonical
trace is its unique trace. Since the distinguished factor is completely
selfless, complete-selflessness tensor permanence makes C*_r(P) selfless
without any exactness assumption on C*_r(H). Thus item 3 implies item 2, and
Robert's theorem gives item 2 implies item 1.

For item 1 implies item 3, each vertex group is a direct factor of P. If
C*_r(G_v) had a nonzero proper ideal I, tensoring the quotient map by the
identity on the complementary direct factor would give a unital noninjective
quotient of C*_r(P). Hence simplicity of C*_r(P) forces simplicity of every
C*_r(G_v). This proves the equivalence.

For the ordinary-anchor variant, assume C*_r(G_(v_0)) is selfless and every
other reduced vertex algebra is exact and simple. Finite minimal tensor
products of the latter algebras are exact, and their directed limit
C*_r(H) is exact. It is simple and uniquely tracial by the preceding group
argument. The exact-second-factor clause of complete-selflessness tensor
permanence therefore makes C*_r(P) selfless.

Finally, if Gamma is finite and every vertex algebra is completely selfless,
iterate complete-selflessness-is-tensor-stable over the finitely many tensor
factors. This gives complete selflessness, not merely the ordinary
selflessness furnished by the one-anchor argument. No countably infinite
complete-selflessness permanence is asserted.
