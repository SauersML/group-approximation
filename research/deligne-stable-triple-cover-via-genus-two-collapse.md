---
rg: 2
id: deligne-stable-triple-cover-via-genus-two-collapse
kind: route
title: Genus-two one-word collapse makes the genus-two triple cover non-hyperlinear, which is the claim at g = 2
target: deligne-stable-triple-cover-is-not-hyperlinear
requires: [deligne-central-mark-hs-collapse, deligne-triple-cover-fd-central-invisibility]
---

`deligne-central-mark-hs-collapse` kills `z` in every vanishing-defect normalized-HS microstate of
`E_3 = E_3^(2)`. A hyperlinear embedding of `E_3` would supply canonical microstates with
`||phi_n(z) - I||_2^2 -> 2`, because `z != 1` has trace `0` in the canonical trace
(`deligne-triple-cover-fd-central-invisibility` records `z != 1`). This is the argument of
`nonhyperlinear-via-deligne-central-mark-collapse`. So `E_3^(2)` is not hyperlinear, which is the
claim with `g = 2`. By `deligne-cover-hyperlinearity-is-monotone-in-genus`, every `E_3^(g)` with
`g >= 2` is then not hyperlinear as well.
