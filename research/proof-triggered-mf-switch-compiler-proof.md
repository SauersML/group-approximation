---
rg: 2
id: proof-triggered-mf-switch-compiler-proof
kind: route
title: Kill one dummy free generator exactly when the machine halts
target: marked-mf-radical-seed-gives-proof-triggered-compiler
requires:
  - mf-radical-functoriality
artifacts:
  - research/artifacts/seeded-self-aware-mf-switch-2026-08-23.md
---

Fix `H=<A|Q>` and `z!=1` in `Res_MF(H)`. On input `e`, output the alphabet
`A disjoint_union {s}`, the mark `z`, and an enumerator that emits `Q`
immediately and emits the single additional relator `s` if and only if the
simulation of `e` halts.

If `e` halts, Tietze elimination of `s` identifies the result with `H`, so the
mark is nontrivial. If `e` does not halt, the presentation has no cross
relator involving `s` and is the free product `H*<s>`. The canonical map
`H->H*<s>` is injective by the free-product normal form, and
`mf-radical-functoriality` sends `z` into the MF radical of the free product.
The alphabet and mark are computable and the relator stream is uniformly
recursively enumerable, so this is the required compiler.
