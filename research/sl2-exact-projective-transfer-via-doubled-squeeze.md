---
rg: 2
id: sl2-exact-projective-transfer-via-doubled-squeeze
kind: claim
title: The doubled conjugation squeeze proves the exact projective transfer at tau-only strength
distinct_from:
  exact-projective-codensity-has-a-uniform-trace-square-gap: that removes scalar phases using perfectness and genuine property (T) of the rank-three subgroup, so it covers only n >= 3; this runs the tau conjugation squeeze one level up on the doubled representation, where the phases cancel identically, and therefore covers the nonperfect rank-one pair SL_2(Z) in SL_2(Z[1/p]) with Selberg's constant.
  projective-commutant-transfer-for-arithmetic-pair: that is the open approximate-representation inequality (PRT1); this establishes its EXACT-representation case for the SL_2 pair with the explicit dimension-free constant K = 4/kappa^2.
  sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair: that supplies co-density and the uniform tau conjugation gap for vectors of M_d; this applies that gap to the doubled space M_(d^2) with the doubled representation, which is what converts trace-square energy into plain commutator energy.
---

Let `Gamma = SL_2(Z[1/p])`, `Lambda = SL_2(Z)` with generating set `S`,
`h in Gamma \ Lambda`, and let `rho : Gamma -> U(d)` be ANY exact
finite-dimensional unitary representation (necessarily of odd
congruence level).  Then for every `U in U(d)`, with
`e(U,V) = 1 - |tr_d([U,V])|^2`,

```text
e(U, rho(h))  <=  (4 / kappa^2) sum_(c in S) e(U, rho(c)),     (DSQ1)
```

where `kappa > 0` is the Selberg `(tau)` conjugation-gap constant of
`sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair`, independent of `d`,
of the level, and of the multiplicity.

This is the exact-representation case of
`projective-commutant-transfer-for-arithmetic-pair` for the SL_2 pair
— the case the perfectness/(T) route cannot reach — with a linear,
dimension-free modulus, as the constrained probe measured
(`experiments/prt1-modulus-probe.json`: ratio `~ 3.0` at two scales,
multiplicity-independent to four digits; the measured `3` is the
Hecke shell index, the proved `4/kappa^2` is an upper bound).

The point of the proof is that no approximate character is ever
extracted: the scalar phases that obstruct the direct argument on the
nonperfect pair cancel identically inside `Ad`, and the established
squeeze applies verbatim one level up.
