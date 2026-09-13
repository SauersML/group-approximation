---
rg: 2
id: radu-lattice-radius-two-mark-forcing-proof
kind: route
title: Fold the tables over the residually finite quotient, read the fold in normal forms, and localize the Garden of Eden
target: radu-lattice-radius-two-pairs-force-the-mark-into-the-radical
requires:
  - radu-bmw-lattice-embeds-in-titz-witzel-kernel
  - radu-lattice-one-sided-pairs-need-residual-coincidences
  - strict-automata-live-on-canonical-table-groups
  - strict-pairs-transfer-to-table-realizations
  - residually-finite-groups-are-surjunctive
  - sofic-groups-are-surjunctive
  - sofic-radical-localizes-garden-of-eden-windows
artifacts:
  - research/artifacts/radu-lattice-b2-anchored-gadget-2026-09-12.md
---

## Why sufficient

1. **Canonical window** (Lemma 1.1). If `tau sigma(y)(g) != y(g)`, then `y` restricted to `g(MS ∪ {1})` is a
   Garden of Eden. The value at `g` depends only on `gMS`, and `tau sigma` fixes the image of `tau`.
   With `S, M ⊆ B_2` this window lies in `B_4`.
2. **Normal forms** (Lemma 2.1). Normal forms `alpha omega` and the square table read backwards give two
   facts. If `g` and `g delta^4` lie in `B_4`, then `g = (zx)^2`. If `ms = (zx)^2` with `m, s in B_2`, then
   `m = s = zx`.
3. **One fold** (Theorem 2.2, items 1 to 3).
   * `Gamma_R / Gamma_0` is residually finite, so over it the pair is two-sided and the reverse table is
     sufficient (Lemmas 2 and 3 of the table-group artifact).
   * Folds come from `Gamma_0 ∩ B_8 = {1, delta^(+-4)}`, so the only fold is `(zx,zx) ~ (xz,xz)`.
   * The fold must occur, because the reverse table over `Gamma_R` is not sufficient.
   * A rule that ignored coordinate `zx` or `xz` would make the fold invisible.
4. **Image** (Theorem 2.2, items 4 and 5).
   * Suppose a configuration agrees on the two folded cells at `g`. It is then constant on the classes
     of the folded table, so `tau sigma` fixes it at `g`.
   * A pattern in `g B_4` that does not separate `g(zx)^2` from `g(xz)^2` extends to a
     `delta^4`-invariant configuration.
5. **Mark** (Theorem 3.1). Localization puts a nontrivial element of `Omega^-1 Omega ⊆ B_8` in
   `Rad(<M>)`. That subgroup lies in the finite residual of `<M>`, hence in `Gamma_0`. By the reading of
   Remark 3.6 the element is `delta^(+-4)`.
6. **Table groups** (Propositions 3.3 and 3.4).
   * Universality gives `U_E -> Gamma_R`.
   * Over the sofic quotient `U_E / Rad(U_E)` the pair is two-sided. So some hinge that folds there but
     not in `Gamma_R` lies in `Rad(U_E)`.
   * Its image lies in `Gamma_0 ∩ B_8`, so it is the mark hinge.
   * With all letters in both memories, the relators of `Gamma_R` are cells of the forward table. This
     gives `U_(E_rho) = Gamma_R`, and any separating transfer map extends to a homomorphism.
