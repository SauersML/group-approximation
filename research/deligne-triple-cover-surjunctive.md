---
rg: 2
id: deligne-triple-cover-surjunctive
kind: claim
title: Deligne's triple cover of Sp4(Z) is surjunctive
refuted_by:
  - deligne-triple-cover-nonsurjunctive
distinct_from:
  finite-normal-subgroups-do-not-affect-surjunctivity: that transfers surjunctivity across every finite normal subgroup; this is its first open instance with residually finite quotient, and proving it would not prove the general statement.
  deligne-triple-cover-is-sofic: soficity of the triple cover would prove this claim by Gromov--Weiss; surjunctivity could hold with the triple cover nonsofic.
artifacts:
  - research/artifacts/deligne-triple-cover-surjunctivity-2026-09-12.md
---

**OPEN.** Let `1 -> C_3 = <z> -> E_3 -> Sp_4(Z) -> 1` be Deligne's connected triple cover, with
`Res_fin(E_3) = C_3` (`deligne-triple-cover-finite-residual-is-center`). Every injective cellular automaton
on `A^(E_3)`, for every finite alphabet `A`, is surjective.

## Attempts

- **Soficity.** `E_3` sofic implies this claim (`deligne-triple-cover-surjunctive-from-soficity`).
  `Rad_sofic(E_3)` is `1` or `C_3`. Soficity is open, and so is hyperlinearity
  (`deligne-sector-gap-is-exactly-nonhyperlinearity`).
- **Characteristic three, linear level: decided.** `k[E_3]` is stably finite for `char k = 3`
  (`deligne-triple-cover-ternary-group-algebras-are-stably-finite`). So there is no strict ternary linear
  automaton, no formalizable strict pair over `F_3^n`, and every strict pair over `F_q^m` has degree
  product at least `q`.
- **Other characteristics, linear level: open.** For `p != 3` the algebra splits into `F_q[Sp_4(Z)]`, which
  is stably finite, and two twisted group algebras of `Sp_4(Z)` with the multiplier of a section (artifact
  Lemma 4.1). The multiplier class is not inflated from any finite quotient.
- **Memory filter.** A strict automaton's memory group `H` contains `z` with `z in Res_fin(H)` and is
  nonsofic (`strict-automata-memory-keeps-finite-normal-kernel-residual`). `H/<z>` is not virtually free
  and not amenable.
- **Counting with exact finite models: dead.** `E_3` is finitely presented and not residually finite, so
  it is not LEF, and some presentation ball has no exact finite model. Counting needs approximate models
  separating `z`, which is soficity (artifact 4.2).
- **Conditional.** If `prime-field-left-inverse-pairs-are-stably-formalizable` holds at `p = 3`, `E_3` is
  surjunctive over every alphabet of size `3^n` (artifact Corollary 2.2(d)).
- **Fixed configurations.** Every strict automaton is bijective on `z`-invariant configurations
  (`surjectivity-descends-to-centralized-coset-quotients`).
- **Products.** Once this claim holds, `E_3 x K` is surjunctive for every `K` in the LEF permanence closure
  (lane w3-products, df56c017aa).
