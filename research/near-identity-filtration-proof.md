---
rg: 2
id: near-identity-filtration-proof
kind: route
title: The commutator estimate for a separated multiplicative filtration
target: near-identity-embedding-forces-residual-nilpotence
requires: []
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

Let `a = 1 + x` with `x in I^r` and `b = 1 + y` with `y in I^s`, both
invertible in `R` with inverses in `1 + I` (as holds in `1 + I` for a
complete filtration, and is assumed here).  Then

    ab - ba  =  xy - yx  in  I^{r+s} ,

so `aba^{-1}b^{-1} = 1 + (ab - ba)b^{-1}a^{-1} in 1 + I^{r+s}`.

Hence `[1 + I^r, 1 + I^s] <= 1 + I^{r+s}`.  With `G <= 1 + I`, induction on
`n` gives `gamma_1(G) <= 1 + I` and
`gamma_{n+1}(G) = [gamma_n(G), G] <= [1 + I^n, 1 + I] <= 1 + I^{n+1}`.

Therefore `∩_n gamma_n(G) <= ∩_n (1 + I^n) = 1 + ∩_n I^n = 1`, which is
residual nilpotence.

If `G` is perfect then `gamma_n(G) = G` for every `n`, so
`∩_n gamma_n(G) = G`, forcing `G = 1`.  A nontrivial perfect group therefore
has no faithful representation of this shape.

`requires: []` is a proof commitment.  Full write-up in
`research/artifacts/kervaire-laudenbach-audit-2026-08-17.md` §H.1.
