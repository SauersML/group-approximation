---
rg: 2
id: bf-n-r-sigma-m-holes-of-f-n-r-pull-back-proof
kind: route
title: "Split-quotient criterion plus Zaremsky's Theorem A transported to r roots"
target: bf-n-r-sigma-m-holes-of-f-n-r-pull-back
requires: []
artifacts:
  - research/artifacts/zp-pure-braided-bht-sigma-2026-09-13.md
---

`pi: bF_{n,r} -> F_{n,r}` splits (`b = 1`). By Meinert (as cited in
arXiv:1803.02717 Citation 1.9, Corollary 2.8 of Meinert 1997), `[psi o pi]` in
`Sigma^m(bF_{n,r})` implies `[psi]` in `Sigma^m(F_{n,r})`.

For `r ≡ 1 mod (n-1)`: by the gap-matching lemma (artifact part 1, Lemma 2)
there is a PL homeomorphism `[0,1] -> [0,r]` with slopes in `<n>` and
breakpoints in `Z[1/n]`. Conjugation by it identifies `F_{n,1}` with
`F_{n,r}` and preserves the germs at the two endpoints, hence `chi_0` and `chi_1`.
Zaremsky's Theorem A (arXiv:1502.02620) says `a chi_0 + b chi_1` with
`a, b >= 0` is not in `Sigma^m(F_{n,1})` for `m >= 2`.
