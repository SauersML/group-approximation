---
rg: 2
id: bf-n-r-sigma-m-holes-of-f-n-r-pull-back-proof
kind: route
title: "Split-quotient criterion plus Zaremsky's Theorem A transported to r roots"
target: bf-n-r-sigma-m-holes-of-f-n-r-pull-back
requires: []
artifacts:
  - research/artifacts/zp-pure-braided-bht-sigma-2026-09-13.md
  - research/artifacts/zp-pure-braided-bht-roots-and-sigma1-2026-09-13.md
---

`pi: bF_{n,r} -> F_{n,r}` splits (`b = 1`). By Meinert (as cited in
arXiv:1803.02717 Citation 1.9, Corollary 2.8 of Meinert 1997), `[psi o pi]` in
`Sigma^m(bF_{n,r})` implies `[psi]` in `Sigma^m(F_{n,r})`.

For the endpoint hull (part 3, Lemma 6): glue a PL map `[0, 1 - 1/n] -> [0, r - r/n]`
to scaled copies of one PL map `[1 - 1/n, 1 - 1/n^2] -> [r - r/n, r - r/n^2]`
(both exist by the gap-matching lemma, residues `0`). The result is a
homeomorphism `h` that conjugates germs `1 - n^k(1-x)` at `1` to germs
`r - n^k(r - y)` at `r`, has finitely many breakpoints away from the right end,
and fixes slopes at `0`. So `f -> h f h^{-1}` is an isomorphism
`F_{n,1} -> F_{n,r}` carrying `chi_0, chi_1` to `chi_0, chi_1`. Zaremsky's
Theorem A (arXiv:1502.02620) gives the holes `a chi_0 + b chi_1`, `a, b >= 0`,
of `Sigma^m(F_{n,1})` for `m >= 2`.
