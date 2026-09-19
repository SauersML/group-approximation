---
rg: 2
id: stw95-countable-exact-filtration-proof
kind: route
title: Use extension permanence at successors and Cu continuity at limits
target: stw95-countable-exact-filtrations-reduce-pure-tensors
requires:
  - stw95-purity-passes-to-sequential-inductive-limits
---

Proceed by transfinite induction on `alpha<=gamma` to prove that
`I_alpha tensor_min B` is pure.  The zero stage is immediate.

At a successor stage, exactness of `B` gives

```text
0 -> I_alpha tensor_min B
  -> I_(alpha+1) tensor_min B
  -> (I_(alpha+1)/I_alpha) tensor_min B -> 0.
```

The ideal is pure by induction and the quotient is pure by hypothesis.
Perera--Thiel--Vilalta extension permanence makes the middle algebra pure.

At a limit ordinal `lambda`, choose an increasing cofinal sequence
`alpha_1<alpha_2<...<lambda`, which exists because `lambda` is countable.
Continuity of the filtration and injectivity of minimal tensoring identify

```text
I_lambda tensor_min B
 =lim_n (I_(alpha_n) tensor_min B).
```

Every stage is pure by induction, so
`stw95-purity-passes-to-sequential-inductive-limits` makes the limit pure.
The induction reaches `I_gamma tensor_min B=A tensor_min B`.

For the final assertion, first fix a simple successor quotient `P` of `A`
and apply the theorem to the filtration of `B`, tensoring by the exact
algebra `P`.  The hypothesis makes all successor products pure, hence
`P tensor_min B` is pure.  Apply the theorem again to the filtration of
`A`, now tensoring by exact `B`.  Its successor products are precisely the
pure algebras just obtained.
