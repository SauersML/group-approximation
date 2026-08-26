---
rg: 2
id: dense-support-character-ratios-of-sl-n-2-vanish
kind: claim
title: Character ratios of SL_N(2) at elements of support proportional to N tend to zero uniformly over nontrivial irreducibles
artifacts:
  - research/dense-support-character-ratios-citation.md
---

**ESTABLISHED by citation** (`dense-support-character-ratios-citation`).

For `g in SL_N(F_2)` write `supp(g)=N-dim ker(g-1)`.  For every
`delta>0`,

```text
sup { |chi(g)|/chi(1) : chi in Irr(SL_N(F_2)) nontrivial,
                        g in SL_N(F_2), supp(g) >= delta N }  -> 0    (DSC1)
```

as `N -> infinity`.

This is the weak, constant-free form of the Larsen--Shalev--Tiep character
bound `|chi(g)| <= chi(1)^(1-c*supp(g)/N)` with an absolute `c>0`, combined
with the fact that every nontrivial irreducible character of `SL_N(F_2)`
has degree at least `2^(N-1)-1`, so that
`chi(1)^(-c*delta) <= (2^(N-1)-1)^(-c*delta) -> 0`.

It is a theorem about finite groups; no property `(T)`, spectral gap,
Kazhdan constant, or expander input appears in it or in its use here.
