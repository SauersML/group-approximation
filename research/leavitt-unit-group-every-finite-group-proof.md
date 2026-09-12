---
rg: 2
id: leavitt-unit-group-every-finite-group-proof
kind: route
title: Permute the leaves of a complete prefix code inside Thompson's V
target: leavitt-unit-group-contains-every-finite-group
requires:
  - leavitt-cylinder-swaps-generate-thompson-in-el
---

- `leavitt-cylinder-swaps-generate-thompson-in-el` gives
  `V <= EL_D(R) <= R^x = L^x`.
- Fix `n >= 2` and the complete prefix code
  `w_1 = 1, w_2 = 01, ..., w_(n-1) = 0^(n-2)1, w_n = 0^(n-1)`.
- For a permutation `sigma` of `{1, ..., n}`, the prefix replacement
  `w_i x -> w_(sigma(i)) x` is a homeomorphism of the Cantor set lying in `V`.
- `sigma` maps injectively to that homeomorphism, and composition matches
  composition up to order reversal, so the image is a copy of `S_n`. Hence
  `S_n <= V <= L^x`.
- By Cayley's theorem every group of order `n` embeds in `S_n`.
- In particular `Z/n <= L^x` for every `n`, so `1/n` lies in
  `Lambda^(L^x)` and the ring is `Q`.
