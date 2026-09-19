---
rg: 2
id: rf-two-generator-pi3-proof
kind: route
title: Symmetrization-stable dyadic rows in the shift right-angled Artin family
target: residual-finiteness-two-generator-recursive-is-pi3-complete
requires:
  - shift-raag-family-is-rf-iff-symmetrized-index-set-closed
  - residual-finiteness-of-enumerated-presentations-is-pi3-complete
---

The upper bound is in
[[residual-finiteness-of-enumerated-presentations-is-pi3-complete]].  For
hardness use [[shift-raag-family-is-rf-iff-symmetrized-index-set-closed]]:
`G_e = G_{J_e}` is residually finite iff `J_e^s = J_e u (-J_e) u {0}` is
profinitely closed in `Z`.  The presentation of `G_e` is recursive
uniformly in `e` (emit `[a, t^i a t^-i]` for `i = 2^x (4j+1)` when the
`(j+1)`-st element of `W_g(e,x)` appears).

Write `D_x = 2^x + 2^{x+1} Z`, the odd multiples of `2^x`, pairwise
disjoint clopen subsets of `Z-hat` covering `Z \ {0}`, and note
`J_e^s n D_x = +-(row x)` where row `x` is `{2^x (4j+1) : j < k_x}`,
`k_x = |W_g(e,x)|`.

*Some row infinite.*  If `k_x` is infinite, then for every `n`, taking
`j = n - 1` gives `2^x (4j + 1) = -3 . 2^x + 2^{x+2} n`, so
`-3 . 2^x in cl(J_e^s)`.  It is an odd multiple of `2^x`, so it could only
lie in `+-(row x)`; but `-3 . 2^x = 2^x (4j+1)` forces `j = -1`, and
`-3 . 2^x = -2^x (4j+1)` forces `4j + 1 = 3`, both impossible.  So
`J_e^s` is not closed and `G_e` is not residually finite.

*All rows finite.*  Let `i in cl(J_e^s)`.  If `i = 0` it is in `J_e^s`.
Otherwise `i in D_x` for one `x`, and since `D_x` is clopen,
`cl(J_e^s) n D_x = cl(J_e^s n D_x) = +-(row x)`, a finite set; so
`i in J_e^s`.  Hence `J_e^s` is closed and `G_e` is residually finite.

With `{e : every W_g(e,x) finite}` `Pi^0_3`-complete (uniform
`Sigma^0_2`-completeness of `FIN`), `RF_rec2` is `Pi^0_3`-hard, hence
complete, and `NONRF_rec2` is `Sigma^0_3`-complete.
