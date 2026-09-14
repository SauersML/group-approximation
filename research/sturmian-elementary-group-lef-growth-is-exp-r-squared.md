---
rg: 2
id: sturmian-elementary-group-lef-growth-is-exp-r-squared
kind: claim
title: For every Sturmian subshift X the LEF growth of EL_3(LC(X,F_2)⋊Z) is exp(Θ(r^2)), with constants independent of the slope
distinct_from:
  elementary-group-lef-growth-separates-subshifts: that predicted a LEF growth class depending on the Diophantine type of the slope; this proves the same class exp(r^2) for every slope, which refutes it.
  subshift-elementary-group-lef-growth-complexity-bounds: that bounds the LEF growth for all minimal X with a √r loss below; this is the exact class on the Sturmian family.
---

**Statement.** Let `X_α` be the Sturmian subshift of irrational slope `α ∈ (0,1)`. Let `G = EL_3(LC(X_α,F_2) ⋊ Z)` with the generators of `subshift-elementary-group-lef-growth-complexity-bounds`, and let `a = ⌊1/min(α, 1−α)⌋`. For `r ≥ 3440 + 1200a`,

`2^(18((r − 3440)/2400)^2) ≤ L_(X_α)(r) ≤ 2^(9(8r+4)^2)`.

So `L_(X_α) ≃ exp(r^2)` for every `α`. The recurrence function of `X_α` is linear only for bounded partial quotients, but LEF growth does not separate Sturmian slopes.

**Key step.**
- Assume `α < 1/2` (swapping the letters exchanges `α` and `1 − α`).
- Let `q_n ≤ 2m < q_(n+1)` be consecutive continued-fraction denominators.
- Put `W = {x_0 = 1, x_(1±q_n) = 1}`, with the sign chosen so that the two arcs overlap. It is a clopen set of measure `‖q_n α‖`.
- By the best-approximation property, `W` has no returns `0 < |t| ≤ 2m`.
- The transvections over `W` cost `O(m)` letters. So the tower copy of `GL_(3(2m+1))(F_2)` forces finite models of order `2^Θ(m^2)`.

**Status: established** by `sturmian-elementary-group-lef-growth-is-exp-r-squared-proof`. The proof is written out and UNREVIEWED; it is queued with sk-referee-2.
