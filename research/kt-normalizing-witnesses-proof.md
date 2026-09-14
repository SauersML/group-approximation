---
rg: 2
id: kt-normalizing-witnesses-proof
kind: route
title: The commutator of a normalizing witness with a compressor centralizes the Kazhdan subgroup
target: kt-normalizing-witnesses-centralize-compressors
requires: []
---

**General statement.** Identify `G` with `sigma(G)`. Let `t in P_Gamma`, so
`t Gamma t^(-1) <= Gamma`, and put `c = t^(-1) h t h^(-1)`. Because `h`
normalizes `G`, `h t h^(-1) in G`, so `c in G`. For `gamma in Gamma`, using
twice that `h` centralizes `Gamma` (once for `gamma`, once for
`t gamma t^(-1) in Gamma`):

```text
c gamma c^(-1) = t^(-1) h t (h^(-1) gamma h) t^(-1) h^(-1) t
              = t^(-1) h (t gamma t^(-1)) h^(-1) t
              = t^(-1) (t gamma t^(-1)) t = gamma.
```

So `c in C_G(Gamma) = 1`, i.e. `h t = t h`. The set of elements of `G`
commuting with `h` is a subgroup containing `P_Gamma`, which generates `G` by
infranormality. Hence `h` centralizes `G`.

**`C_G(Gamma) = 1` for the binary Kun--Thom pair.** Write `R_+ = F_2[x_1..x_d]`,
`R = F_2[x^(+-1)]`, and elements of `G` as `(m,A)` with `m in EL_r(R)`,
`A in SL_d(Z)` acting on `R` by monomial substitution, so that
`(m,A)(n,I) = (m (A.n), A)`. Suppose `(m,A)` commutes with every `(e_ij(p),I)`,
`p in R_+`, `i != j`. Then `m e_ij(A.p) m^(-1) = e_ij(p)`.

- Taking `p = 1` shows that `m` commutes with every `e_ij(1)`, so `m = lambda I`
  with `lambda in R^x`.
- Since `m in EL_r(R) <= SL_r(R)`, `lambda^r = 1`. The units of
  `F_2[x^(+-1)]` are the monomials `x^a`, so `a = 0` and `m = I`.
- Then `e_ij(A.p) = e_ij(p)` for all polynomials `p`, so `A` fixes every
  `x_k`, i.e. `A = I`.

Infranormality of `Gamma` is part of Kun--Thom Theorem E
(`kun-thom-nonsofic-wreath`).
