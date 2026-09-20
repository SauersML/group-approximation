---
rg: 2
id: laurent-steinberg-stability-from-free-algebra-stability
kind: route
title: Descend flexible stability of E_n of a free algebra to its relative quotient St_n(F_q[t,t^-1])
target: laurent-steinberg-group-is-flexibly-hs-stable
requires:
  - free-algebra-elementary-group-is-flexibly-hs-stable
  - relative-elementary-quotients-inherit-flexible-hs-stability
  - free-algebra-relative-quotient-is-laurent-steinberg
---

Let `(A, n, k)` be given by `free-algebra-elementary-group-is-flexibly-hs-stable`, so that
`E_n(S)` is flexibly HS stable for `S = A<x_1..x_k>`, with `n >= 3` and `k >= 4`. Choose `q = 3` if
`A = Z` or `p = 3`, and `q = p^2` otherwise. In every case `q >= 3` has characteristic `p` when
`A = F_p`. (For `A = Z`, any prime power `q >= 3` works.)

- By `free-algebra-relative-quotient-is-laurent-steinberg`, there is a finitely generated two-sided
  ideal `I` of `S` with `E_n(S)/E_n(S,I) ≅ St_n(F_q[t,t^-1])`.
- `S` is a finitely generated ring. So by `relative-elementary-quotients-inherit-flexible-hs-stability`,
  `E_n(S)/E_n(S,I)` is flexibly HS stable.
- Flexible HS stability is invariant under isomorphism, so `St_n(F_q[t,t^-1])` is flexibly HS
  stable, with `n >= 3` and `q >= 3`. ∎

The ratio-one variant passes along the same route, since the descent node keeps dimension
control.
