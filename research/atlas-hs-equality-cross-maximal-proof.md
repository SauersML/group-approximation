---
rg: 2
id: atlas-hs-equality-cross-maximal-proof
kind: route
title: Identify the HS normalizer cell and apply classical collision collapse
target: atlas-hs-equality-escape-must-cross-s8-maximals
requires:
  - atlas-a8-index-991-to-2200-reaches-hs-s8-derived
  - atlas-a4-19243-classical-collapse
---

The ambient classification gives `N_HS(H)=M~=S8` and says `M/H` induces the
outer automorphism of `H~=A8`.  Therefore conjugators in `M` exhaust both
relative marking parities on the unchanged subgroup `H`.

The classical-collapse theorem states that no two automorphism markings of
one `A8` satisfy the packet together with collision 19243.  Hence every
conjugator in `M` is excluded.  Since `M` is maximal and self-normalizing in
the simple group `HS`, `g notin M` also implies `M^g!=M`; since
`N_HS(H)=M`, it implies `H^g!=H`.  This proves `(HSC1)`.

