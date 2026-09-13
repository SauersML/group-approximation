---
rg: 2
id: kazhdan-compression-instances-have-infinite-vcd-proof
kind: route
title: Conjugate the commuting pair into the compressed subgroup and iterate
target: kazhdan-compression-instances-have-infinite-vcd
requires: []
---

**Lemma (internal products).**
- If `A, B <= G` commute and `A cap B = 1`, then `(a,b) |-> ab` is an isomorphism
  `A x B -> AB`.
- If moreover `B` is itself an internal direct product `B_1 x B_2`, then `AB` is the internal
  direct product `A x B_1 x B_2`.
- Conjugation preserves commuting and trivial intersection.

## Proof of (N1)

Induction on `n`.

*Base.* Conjugating `[Gamma,J] = 1` and `Gamma cap J = 1` by `t` gives the same relations for
`t Gamma t^-1` and `J_1`. Both lie in `Gamma` by hypothesis, so `Gamma >= J_1 x t Gamma t^-1` is
an internal direct product.

*Step.* Conjugating the base case by `t^n` gives
`t^n Gamma t^-n >= J_(n+1) x t^(n+1) Gamma t^-(n+1)`, an internal direct product. The subgroup
`t^n Gamma t^-n` commutes with `J_1 ... J_n` and meets it trivially, so every subgroup of it does
too. Hence

```text
Gamma >= J_1 x ... x J_n x J_(n+1) x t^(n+1) Gamma t^-(n+1)
```

is internal. `QED`

## Proof of (N1')

Put `A = q Gamma q^-1 <= Gamma`. It commutes with `J <= Gamma` and meets it trivially, so
`Gamma >= J x A`. Conjugating by `q` gives `A >= q J q^-1 x q^2 Gamma q^-2`, internally.
Substituting and iterating exactly as in (N1) gives the displayed tail. `QED`

## Proof of (N2)

By (N1) or (N1'), `G` contains an internal direct product of `n` copies of `J`.

- **Infinite order.** If `j in J` has infinite order, `G` contains `<j>^n ~= Z^n` for every `n`.
  Let `G_0 <= G` have finite index. Then `Z^n cap G_0` has finite index in `Z^n`, so it is again
  `~= Z^n`, and `cd G_0 >= cd Z^n = n`. Monotonicity holds because `ZG_0` is free over the group
  ring of any subgroup. `Z^n` acts freely and cocompactly on `R^n`, so `H^n(Z^n; Z) = Z`. Hence
  `cd G_0 = infinity`.
- **Torsion.** Otherwise `J != 1` is a torsion group, so it has an element of some prime order
  `p`, and `G` contains `(Z/p)^n` for every `n`. Let `G_0 <= G` have finite index and finite
  cohomological dimension. Then `G_0` is torsion-free, because `cd(Z/p) = infinity`. For a finite
  `F <= G`, `F cap G_0 = 1`, so `f |-> f G_0` is injective on `F` and `|F| <= [G:G_0]`. This is
  false for `F = (Z/p)^n` with `p^n > [G:G_0]`. `QED`

## Consequences

- **The criteria.** In `openai-expander-matching-criterion` the conclusion is that `J` is LEF, so
  a certificate of nonsoficity needs `J` not LEF, in particular `J != 1`. In
  `one-sided-compression-nonsofic-criterion` the witness `J` is likewise not LEF. (N2) applies.
- **Kun--Thom wreath products.** The lamp group `directSum_(G/Gamma) Z/2` contains `(Z/2)^n` for
  every `n`, because `G/Gamma` is infinite. See the infinite-index argument in
  `vcd-two-groups-contain-no-kazhdan-commuting-pairs`.
- **The recorded Kun--Thom doubles.** They contain `EL_r(F_q[x^(±1)])`, whose root subgroup
  `e_12(F_q[x^(±1)])` is an infinite elementary abelian `p`-group. The torsion case of the
  argument above applies to it.
