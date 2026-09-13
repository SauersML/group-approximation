---
rg: 2
id: closed-mcg-aut-embedding-via-punctured-host
kind: route
title: Closed-surface mapping class groups embed in some Aut(F_n) if a finite-index subgroup embeds in a punctured-surface mapping class group
target: every-closed-surface-mcg-embeds-in-some-aut-free-group
requires:
  - closed-mcgs-virtually-embed-in-punctured-mcgs
  - punctured-surface-mcgs-virtually-embed-in-aut-free-groups
  - aut-free-embeddability-passes-to-finite-index-overgroups
  - low-genus-closed-mcgs-embed-in-aut-free-groups
---

- **g ≤ 2.** `low-genus-closed-mcgs-embed-in-aut-free-groups`.
- **g ≥ 3.**
  1. By `closed-mcgs-virtually-embed-in-punctured-mcgs`, a finite-index
     `L ≤ MCG(S_g)` embeds in the extended mapping class group of a finite-type
     surface `Σ′` with a puncture or boundary component.
  2. By `punctured-surface-mcgs-virtually-embed-in-aut-free-groups`, a finite-index
     `M ≤ MCG^±(Σ′)` embeds in some `Aut(F_k)`.
  3. The preimage in `L` of `M` has finite index in `MCG(S_g)` and embeds in
     `Aut(F_k)`.
  4. Item 2 of `aut-free-embeddability-passes-to-finite-index-overgroups` embeds
     `MCG(S_g)` in some `Aut(F_n)`.
