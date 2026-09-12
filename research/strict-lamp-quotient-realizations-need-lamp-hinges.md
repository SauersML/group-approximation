---
rg: 2
id: strict-lamp-quotient-realizations-need-lamp-hinges
kind: claim
title: A strict realization over a lamp quotient of the Kun--Thom wreath must read a nonzero lamp relation of the quotient among its forward coincidences
distinct_from:
  strict-pairs-transfer-to-table-realizations: that pushes strict certificates forward along homomorphisms and folds windows in surjunctive quotients; this pulls a realization back along the quotient map from a surjunctive group and locates a forward hinge in the kernel.
  garden-of-eden-windows-fold-modulo-every-hinge-closure: that places window differences in reverse hinge closures; this places a forward hinge word inside the lamp submodule that is quotiented out.
artifacts:
  - research/artifacts/kun-thom-lamp-quotient-hosts-2026-09-12.md
---

**ESTABLISHED** by `strict-lamp-quotient-realizations-lamp-hinge-proof`.

Let `W` be the Kun--Thom coset wreath, `U <= P` any lamp submodule, and `rho` a realization of a
design over `H_U = W/U` whose automaton is strict: `E_rho` is forward sufficient and `F_rho` is
not reverse sufficient. Then for every lift `rho~` of `rho` to `W` with `rho~(1) = 1`:
- `E_(rho~)` is not forward sufficient;
- some coincidence of `E_rho` fails for `rho~`, and its hinge word is a nonzero element of `U`.

When `U <= K_even` that hinge is a fibre-even lamp configuration with trivial `G`-part, invisible
in every sofic image of `W`. So a strict design over a lamp quotient must build a relation of
`U` into its decoder identity.

The same argument works for any surjunctive group `W` and normal subgroup `U`: a strict
realization over `W/U` has, in every lift, a forward hinge word in `U \ {1}`.

Proof: Theorem D of the artifact.
