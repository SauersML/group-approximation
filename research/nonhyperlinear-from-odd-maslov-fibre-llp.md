---
rg: 2
id: nonhyperlinear-from-odd-maslov-fibre-llp
kind: route
title: Odd Maslov fibre LLP alone makes the Deligne triple cover non-hyperlinear
target: non-hyperlinear-group
requires:
  - sp4-mod3-twisted-fibres-have-llp
  - odd-maslov-twisted-fibres-have-no-amenable-trace
  - llp-makes-hyperlinear-traces-amenable
  - thom-central-corner-criterion
---

Let `E_3` be Deligne's triple cover and let `A_alpha` be either nontrivial
central-character fibre.  Suppose `E_3` were hyperlinear.  Thom's
central-corner criterion would make the canonical twisted trace on
`A_alpha` hyperlinear.  If
`sp4-mod3-twisted-fibres-have-llp` holds, then
`llp-makes-hyperlinear-traces-amenable` makes that trace amenable.  This
contradicts `odd-maslov-twisted-fibres-have-no-amenable-trace`.

Therefore LLP of the odd mod-three fibre by itself forces the explicit
finitely presented group `E_3` to be non-hyperlinear.  Unlike
`non-hyperlinear-from-e3-fibre-llp`, this route does **not** require LLP of
the untwisted full group C-star algebra `C^*(Sp_4(Z))`: the contradiction is
already localized in one nontrivial twisted central corner.
