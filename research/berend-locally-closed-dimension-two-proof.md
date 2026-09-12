---
rg: 2
id: berend-locally-closed-dimension-two-proof
kind: route
title: Separate closed sets from the generic point and reduce them to finite orbit quotients
target: berend-locally-closed-primitive-dimension-is-two
requires:
  - berend-primitive-spectrum-has-one-faithful-generic-point
  - berend-proper-quotients-have-decomposition-rank-at-most-two
artifacts:
  - research/artifacts/stw99-lxxxvi-berend-frontier-2026-08-30.md
---

Every closed subset of a primitive spectrum is `hull(J)` for an ideal
`J`.  It omits `0` exactly when `J != 0`.  In that case
`hull(J) = Prim(A/J)`, and the proper-quotient theorem writes `A/J` as a
finite direct sum

`direct_sum_i M_{n_i}(C(Y_i))`,  with `Y_i closed in T^2`.       `(BLP1)`

Hence every closed set avoiding `0` is a finite union of compact metrizable
spaces of covering dimension at most two.

Since `0` is dense, every nonempty open subset of `Prim(A)` contains `0`.
Now write a locally closed Hausdorff subspace as `S = U cap C`, with `U`
open and `C` closed.  If `0 notin C`, then `(BLP1)` makes `S` a metrizable
subspace of a finite union of spaces of dimension at most two, so
`dim(S) <= 2`.  If `0 in C` and `S` is nonempty, then `0 in U`, hence
`0 in S`; moreover `0` is dense in `S`.  A singleton is closed in a
Hausdorff space, so this forces `S = {0}`.  This proves `(BLH1)`.

For a finite orbit `O`, the hull of the orbit-quotient kernel is

`Prim(C(O) ⋊ Z^2) = dual(Stab(O)) = T^2`,                   `(BLP2)`

a closed Hausdorff stratum.  Thus the upper bound is sharp.

There is also an exact ideal-filtration consequence.  The primitive
spectrum of every nonzero ideal is a nonempty open subset and therefore
still contains the generic point `0`.  Passing to a proper quotient can
isolate only finitely many closed orbit strata, while passing to a nonzero
ideal retains the faithful accumulation core and deletes at most such a
finite closed family.  An ideal filtration based only on finite-orbit
type-I layers therefore cannot reduce `dr(A)` to the known quotient bounds:
one residual layer always contains the original generic-point difficulty.
