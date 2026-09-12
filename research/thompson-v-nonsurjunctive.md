---
rg: 2
id: thompson-v-nonsurjunctive
kind: claim
title: Thompson's group V carries an injective non-surjective cellular automaton
distinct_from:
  thompson-v-surjunctive: that is the positive root for V; this is its negation, the counterexample form, which would refute it.
  leavitt-unit-group-nonsurjunctive: that asks for a strict automaton over the binary Leavitt unit group; this asks for one over its subgroup V, which is stronger and ascends to that group.
  thompson-v-not-sofic: that is nonsoficity of V; a strict automaton over V proves it by Gromov--Weiss, while a nonsofic V need not be nonsurjunctive.
artifacts:
  - research/artifacts/thompson-v-linear-counterexample-targets-2026-09-12.md
---

**OPEN.** For some finite alphabet `A` there is a cellular automaton `A^V -> A^V` over
Thompson's group `V = G_(2,1)` that is injective and not surjective.

Consequences:
- `V` is not sofic (`thompson-v-not-sofic-from-nonsurjunctivity`);
- the binary Leavitt unit group is not surjunctive, by ascent along `V <= R^x`
  (`thompson-v-nonsurjunctivity-ascends-to-leavitt-units`). So Gottschalk's conjecture fails.

## Attempts

- **Linear route.** `thompson-v-nonsurjunctive-from-direct-finiteness-failure`: a failure of
  direct finiteness of `F_p[V]` suffices. The concrete `F_3` target is
  `thompson-v-ternary-swap-idempotent-is-full`.
- **Kazhdan compression.** Dead inside `V`: every Kazhdan subgroup of `V` is finite
  (`thompson-v-has-no-rigid-compression-defect`). Any nonsoficity that a strict automaton over
  `V` carries must come from a mechanism with no property (T).
- **Cantor-orbit encodings.** Dead: `full-shift-maps-to-infinite-stabilizer-coset-shifts-are-constant`.
  Compressions such as `V_(0*) > V_(00*)` give strict self-maps only on the subshift of
  configurations constant on the left cosets `gH`, `H = V_(0*)` (`y -> y o psi` with `psi(gH) = g u^-1 H`),
  never on the full shift.
- **Design filters.** A candidate must pass the landed filters: nonsofic forward core,
  triangular tables, holonomy normal form, amenable decoder memory, measure distortion. Its
  memory group must be a nonsofic subgroup of `V`.
