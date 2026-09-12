---
rg: 2
id: mf-vs-tracial-radical-strict-gap-proof
kind: route
title: Transport puts the lamp commutator in the shadow and the diffuse model keeps it out of the radical
target: mf-vs-tracial-radical-strict-gap
requires: [infinite-cyclic-compression-lamp-mf, kazhdan-asymptotic-commutant-transport]
artifacts:
  - GroupApproximation/Sofic/IntrinsicCompressionMFRadical.lean
---

## Why sufficient

The root lamp `c` of `W_Z` commutes with `t L t^{-1}`, so
`z = t^{-1} c t` commutes with `L`, and `t z t^{-1} = c`.  Thus
`[c, g] = [t z t^{-1}, g]`, `g in L`, is literally a generator of the
intrinsic compression-centralizer defect of the pair `(W_Z, L)`.  Since
`L` has property (T), the formalized transport of asymptotic commutants
(`kazhdan-asymptotic-commutant-transport`, kernel-checked in the intrinsic
form in `GroupApproximation/Sofic/IntrinsicCompressionMFRadical.lean`)
makes every such generator vanish in the normalized-HS ultraproduct of
every operator-norm almost representation:

```text
[g, c] in R_{infty->2}(W_Z).
```

By `infinite-cyclic-compression-lamp-mf`, `W_Z` has a faithful corona
representation, so `Rad_MF(W_Z) = 1`, while `[g, c] != 1` for
`g in L \ tLt^{-1}` because the two lamp sites are distinct.  Hence the
inclusion of the radicals is strict, witnessed by `[g, c]`.

## Formalized layer (2026-08-15)

The MF-side input of this route — faithfulness for `W_Z` — remains
paper-level, but its locality core is now kernel-checked:
`GroupApproximation/Sofic/IntegerLampSurvival.lean` proves the
integer-lamp-by-telescope layer operator-MF
(`isOperatorMF_integerLampTelescope`; generic criterion
`isOperatorMF_lampWreath`) whenever the base is residually finite and
the compression has finite index.  The gap statement itself still
consumes the full `W_Z` with the shift, i.e. the slow-bump corona
model of [[infinite-cyclic-compression-lamp-mf]]; formalizing that
model is the one remaining analytic step on the survival side.
