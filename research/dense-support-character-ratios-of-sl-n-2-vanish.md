---
rg: 2
id: dense-support-character-ratios-of-sl-n-2-vanish
kind: claim
title: Character ratios of SL_N(2) at elements of support proportional to N tend to zero uniformly over nontrivial irreducibles
artifacts:
  - research/dense-support-character-ratios-citation.md
---

**ESTABLISHED by citation** (`dense-support-character-ratios-citation`).

For `g in SL_N(F_2)` write

```text
supp(g)=min_(lambda in algebraic closure of F_2)
          codim ker(g-lambda I),
```

the codimension of its largest eigenspace.  For every `delta>0`,

```text
sup { |chi(g)|/chi(1) : chi in Irr(SL_N(F_2)) nontrivial,
                        g in SL_N(F_2), supp(g) >= delta N }  -> 0    (DSC1)
```

as `N -> infinity`.

This is the constant-free consequence of Larsen--Shalev--Tiep's uniform
bound

```text
|chi(g)|/chi(1) < 2^(-sqrt(supp(g))/481).
```

If `supp(g)>=delta N`, the right side tends to zero uniformly.  No
minimal-character-degree estimate is needed.

It is a theorem about finite groups; no property `(T)`, spectral gap,
Kazhdan constant, or expander input appears in it or in its use here.
