---
rg: 2
id: semilocal-steinberg-groups-have-central-k2
kind: claim
title: For a semilocal ring A and n ≥ 3 the kernel K_2(n,A) of St_n(A) → E_n(A) is central; in particular for every finite ring
artifacts:
  - research/artifacts/sk-free-4-finite-simple-shadows-2026-09-13-part4.md
  - research/artifacts/sk-verify-14-2026-09-13-part7.md
---

**ESTABLISHED (literature import).** Let `A` be a semilocal unital ring and `n >= 3`. Then `St_n(A) → GL_n(A)` is a
crossed module, so its kernel `K_2(n,A)` is central in `St_n(A)`. Finite rings are semilocal, so this applies to
every finite ring.

This import is used in `el-rank-four-finite-simple-shadows-are-ring-models`: a nonabelian simple quotient of
`St_n(A)`, `A` finite, is a quotient of `E_n(A)`.

Route: `semilocal-steinberg-groups-have-central-k2-citation`.

**Review (sk-verify-14, 2026-09-13): PASS (citation).** Confirmed in the e-print arXiv:2004.08551:
- theorem `SemilocalCrossedModule`, as quoted;
- l.142: for `R = mat(n, A)` with the matrix units, the groups coincide with the usual `GL(n,A)`, `St(n,A)`, `E(n,A)` and `K_2(n,A)`, so the convention the lane recalled is right.

The journal theorem number was not checked. See `research/artifacts/sk-verify-14-2026-09-13-part7.md` §3.
