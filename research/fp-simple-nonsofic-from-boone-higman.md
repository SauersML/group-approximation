---
rg: 2
id: fp-simple-nonsofic-from-boone-higman
kind: route
title: Feed the rank-twelve Leavitt group to Boone-Higman and inherit nonsoficity upward
target: fp-simple-nonsofic-group
requires: [boone-higman-conjecture, binary-leavitt-elementary-group-is-simple, d-ary-leavitt-groups-nonsofic-over-finite-fields, rank-twelve-leavitt-elementary-wp-decidable, sofic-passes-to-subgroups]
artifacts:
  - research/artifacts/boone-higman-nonsofic-envelope-2026-09-11.md
---

Put `R=L_(F_2)(1,2)` and `H=EL_12(R)`.

## The input is admissible, simple and nonsofic

* `binary-leavitt-elementary-group-is-simple` gives `EL_n(R)=GL_n(R)`
  nontrivial and simple for every `n >= 3`; take `n=12`.
* `d-ary-leavitt-groups-nonsofic-over-finite-fields` gives, for a finite field
  `k` and an algebra carrying a `d`-ary Leavitt family, that every
  `EL_{m+1}` with `m >= 1` is nonsofic. Specialize to `k=F_2`, `d=2`,
  `A=L_(F_2)(1,2)` and `m=11`: `H` is not sofic.
* `rank-twelve-leavitt-elementary-wp-decidable` gives that `H` is finitely
  generated, infinite, and has decidable word problem.

So `H` is a finitely generated group with solvable word problem, which is the
hypothesis of `boone-higman-conjecture`.

## The envelope inherits nonsoficity

Assume the conjecture. It supplies a finitely presented simple group `K` and
an embedding

```text
iota : H -> K.                                               (FSB1)
```

`H` is not sofic, and `iota` is injective, so the contrapositive form
`(SPS1)` of `sofic-passes-to-subgroups` gives that `K` is not sofic: were `K`
sofic, soficity would pull back along `iota` to `H`.

`K` is therefore finitely presented, simple and nonsofic, which is
`fp-simple-nonsofic-group`. `∎`

## Scope

The argument uses only that `H` is finitely generated, has solvable word
problem, and is nonsofic; simplicity of `H` is not needed for this route and
is cited only to record what the input is. Any finitely generated nonsofic
group with solvable word problem would serve, and
`d-ary-leavitt-groups-nonsofic-over-finite-fields` supplies a whole family of
them.

The same envelope also has full MF radical, by
`fp-simple-full-mf-radical-from-boone-higman` applied to the same `H`. That is
a separate conclusion from a separate hypothesis on `H`, and neither
approximation property implies the other here.
