---
rg: 2
id: fpbs-power-p-deficiency-excludes-property-t-proof
kind: route
title: Truncate the presentation, apply openness of (T), then Lackenby largeness
target: fpbs-power-p-deficiency-excludes-property-t
requires:
  - fpbs-shalom-property-t-is-open
  - fpbs-power-p-deficiency-schreier-bound
  - fpbs-lackenby-derived-p-series-largeness
artifacts:
  - research/artifacts/fpbs/docs/power-p-deficiency-excludes-t-2026-09-11.md
---

Written deduction, lane `fixed-price-2`, 2026-09-11. The full argument is
Section "Proof" of the artifact.

1. The truncations `G_k = <X | r_1..r_k>` converge to `Gamma` as marked groups.
2. Openness makes some `G_k` Kazhdan if `Gamma` is.
3. Deficiency only rises when relators are dropped, so `def_p(G_k) > 0`. The
   Schlage-Puchta inequality then gives `d_p(D_i) > def_p(G_k)[G_k:D_i]` along
   the derived `p`-series.
4. Lackenby's Theorem 1.12 makes the finitely presented `G_k` `p`-large.
5. A `p`-large group has a finite index subgroup with infinite abelianization.
   That is incompatible with (T), which passes to finite index subgroups and
   forces finite abelianization.

No step uses finite presentability of `Gamma` itself.
