---
rg: 2
id: bernoulli-window-folner-ratio-bound-proof
kind: route
title: Decode the sites of a finite set from the codewords over its right translate and count
target: bernoulli-window-codeword-folner-ratio-bound
requires: []
artifacts:
  - research/artifacts/rokhlin-window-random-order-transport-2026-09-12.md
---
Artifact Section 5, Proposition 6.

1. For finite `S`, subadditivity and translation give `|S| k log q = H(x|_S) <= H(y_(SF)) + sum_(s in S) H(x(s) | y_(sF)) <= |SF| H(y_1) + |S| H(x(1) | y_F)`.
2. Take the infimum over `S`. Since `lambda >= 1`, this gives the bound on `Phi`.
3. If `|SF| <= (1 + eps)|S|`, then `S` is almost invariant under right multiplication by `F f_0^-1`, so some left coset of `<F F^-1>` carries a right Følner set.
4. Conversely, right Følner sets of `<F F^-1>` give ratio near `1`.
