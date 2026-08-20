---
rg: 2
id: two-generator-amitsur-levitzki-dimension-oracle-proof
kind: route
title: Separate the permutation monomials and invoke the standard polynomial identity
target: two-generator-amitsur-levitzki-dimension-oracle
requires: []
artifacts:
  - research/artifacts/kleene-self-destroying-hs-pcp-boone-2026-08-20.md
---

For a permutation `sigma`, the corresponding summand of `p_n` is the free
monomial

```text
x y^(sigma(1)) x x y^(sigma(2)) x ... x y^(sigma(2n)) x.
```

The `xx` separators recover the ordered exponent list, so distinct
permutations give distinct monomials.  None cancel, proving `(ALO2)`.

Amitsur--Levitzki says that `M_d(C)` satisfies the standard identity `s_(2d)`.
Substituting `rho(u_1),...,rho(u_(2d))` proves `(ALO3)`.

The free associative algebra embeds in its universal free skew field.  Every
nonzero `p_n` is invertible there, so mapping `q_n,q'_n` to its right and left
inverse gives a nonzero model of `(ALO4)`.  A unital representation into
`M_d(C)` would send the `n=d` relation `p_dq_d=1` to `0=1`, which is
impossible.
