---
rg: 2
id: cubulated-hyperbolic-in-brin-thompson-proof
kind: route
title: Cubulated hyperbolic groups embed in some nV by Agol plus Belk-Bleak-Matucci
target: cubulated-hyperbolic-groups-embed-in-some-brin-thompson-group
requires:
  - cubulated-hyperbolic-groups-are-virtually-special
  - virtually-special-groups-embed-in-some-brin-thompson-group
---

1. By `cubulated-hyperbolic-groups-are-virtually-special` (Agol), such a
   hyperbolic group `G` has a finite-index subgroup `F` with `X/F` a compact
   special cube complex.
2. By Haglund–Wise, recorded in the same claim, `F = π_1(X/F)` embeds in a
   finitely generated right-angled Artin group. So `G` virtually embeds in that
   group.
3. By `virtually-special-groups-embed-in-some-brin-thompson-group`
   (Belk–Bleak–Matucci, Corollary 1.5 and the remark after Corollary 1.3), `G`
   embeds in nV for some n.
