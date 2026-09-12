---
rg: 2
id: stw01-problem-i-via-three-projection-algebra
kind: route
title: Settle Problem I on the universal C*-algebra of three projections
target: stw99-problem-i-quasitraces-are-traces
requires:
  - stw01-three-projection-algebra-quasitraces-are-traces
---

If every bounded 2-quasitrace on `P_3 = C^2 * C^2 * C^2` is a trace, then Problem I
holds. Full proof: `research/artifacts/stw01-three-projection-universal-test-2026-09-12.md`.

Outline.
1. If Problem I fails, Gow's Theorem A gives a type `II_1` AW*-factor `M` that is not
   W*.
2. Its canonical quasitrace `tau` is not additive. Otherwise it would be a faithful
   state that is completely additive on projections, and Gow Corollary 3.10 would
   make `M` W*.
3. Norm continuity, density of finite-spectrum elements, and telescoping give a
   witness `tau(y + beta q) != tau(y) + beta tau(q)`, with `y >= 0` of finite
   spectrum, `q` a projection and `beta > 0`.
4. Shifting by a scalar makes the spectral family of `y` a positive combination of
   `k-1` orthogonal projections. In `M_2(M)` the explicit dilation
   `p = diag(P, 0)`, `p' = [[A, S], [S, P - A]]` recovers `y (+) 0` as `g(p p' p)`.
5. The defect lives in `C*(1, p, p', q (+) 0)`, a quotient of `P_3`. A 2-quasitrace
   extension on `M_2(M)` (Blackadar–Handelman) restricts to this subalgebra and
   pulls back to a non-additive bounded 2-quasitrace on `P_3`.

The converse is trivial, so the route is an equivalence.
