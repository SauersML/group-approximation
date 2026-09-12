---
rg: 2
id: fpbs-power-p-deficiency-excludes-property-t
kind: claim
title: No group with a presentation of positive power p-deficiency has property (T)
distinct_from:
  fpbs-power-p-deficiency-schreier-bound: that is the imported inequality giving positive p-gradient; this is the derived theorem that such groups are never Kazhdan, even with infinitely many relators.
  fpbs-lackenby-derived-p-series-largeness: that is Lackenby's theorem for finitely presented groups; this extends the exclusion of (T) to infinitely presented and torsion groups through openness of (T).
artifacts:
  - research/artifacts/fpbs/docs/power-p-deficiency-excludes-t-2026-09-11.md
---

**ESTABLISHED (written deduction).** Let `p` be prime, and let `Gamma` have a
presentation `(X,R)` with `X` finite, `R` possibly infinite, and
`|X| - 1 - sum_(r in R) p^(-nu_p(r)) > 0`. Then `Gamma` does not have property
(T).

**Proof sketch.**
1. The finite truncations `G_k` of the presentation converge to `Gamma` as
   marked groups.
2. If `Gamma` had (T), openness (`fpbs-shalom-property-t-is-open`) would make
   some `G_k` Kazhdan.
3. That `G_k` is finitely presented with `def_p(G_k) >= def_p(X,R) > 0`, so its
   derived `p`-series has linear mod-`p` homology growth
   (`fpbs-power-p-deficiency-schreier-bound`).
4. So `G_k` is `p`-large (`fpbs-lackenby-derived-p-series-largeness`), which
   contradicts (T).

The full proof is in the linked artifact.

**Why this matters for Fixed Price.** It kills the most direct way to build
`fpbs-kazhdan-positive-rank-gradient`. Power `p`-deficiency is the known way to
force positive `p`-gradient in infinitely presented and torsion groups
(Schlage-Puchta, Osin). A Kazhdan group of that kind would have supplied a
Farber chain of positive rank gradient; see
`fpbs-kazhdan-gradient-via-power-p-deficiency`.

The weighted Golod-Shafarevich condition is not excluded: Ershov and
Jaikin-Zapirain give Golod-Shafarevich Kazhdan groups. So the exclusion is
specific to power deficiency.
