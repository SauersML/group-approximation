---
rg: 2
id: leavitt-units-carry-injective-invariant-output-automaton
kind: claim
title: Some injective automaton over the Leavitt unit group has output constant on right cosets of a finite subgroup
artifacts:
  - research/artifacts/gottschalk-sofic-radical-localization-2026-09-11.md
---

**OPEN.** Let `G = L_(F_2)(1,2)^x`. Exhibit a finite alphabet `A`, a finite
subgroup `H != 1` of `G`, and an injective cellular automaton `tau` on `A^G` with

    tau(x)(gh) = tau(x)(g)       for all x, g, and h in H.

Such a `tau` misses every configuration that is not right-`H`-invariant, so it
is strict and refutes `leavitt-unit-group-nonsurjunctive`. The certificate needs
only a left-inverse automaton; the Garden of Eden is automatic, any two-cell
pattern on `{1,h}` with distinct symbols.

## Why this architecture

- **Counting leaves it alive over this group and no other kind.** By
  `invariant-output-injective-automata-need-invisible-symmetry`, `H` must lie in
  the sofic radical of the effective memory group. By
  `leavitt-unit-group-has-only-trivial-sofic-morphisms`, every finite subgroup
  of `G` qualifies once the memory generates `G`, or any `EL_n(R)` with
  `n >= 3`. No almost-multiplicative permutation model separates `h` from `1`.
- **It is genuinely nonlinear.** By `linear-invariant-output-automata-fail-augmentation`,
  an involution-invariant output over `F_2` is impossible for linear rules.
  Odd `|H|` only returns to the Kaplansky corner questions.

## Necessary conditions a candidate must meet

1. The effective memory `M` satisfies `HM = M`, and the local rule is invariant
   under `m -> hm`.
2. The diagonal restriction of the local rule permutes `A`, because constants
   map injectively to constants.
3. `<M>` is not surjunctive. In particular it must not be sofic, and `H` must
   be invisible in it.
4. No surjunctive guard subgroup meets every monomial, by
   `surjunctive-guard-subgroups-force-surjectivity`.

## Attempts

- *Linear rules.* Dead for `|H|` even over `F_2` by augmentation. For odd
  `|H|` they are the corner compression `c e b = 1` of the Kaplansky lane.
- *Symmetrize a bijective automaton.* Take `Pi` bijective and
  `Sym(z)(g) = s(z(g), z(gw))` with `s` symmetric. Then `Sym o Pi` sends
  `Pi^-1(z)` and `Pi^-1(z o R_w)` to the same output, and these are distinct
  whenever `z != z o R_w`. So a pointwise symmetric reduction after any
  bijection is never injective. The invariance must be produced jointly with
  the mixing, not after it.
- *Counting along permutation models.* Over `G` every model folds each `h` onto
  `1`, so no counting argument decides this claim in either direction.
  Recorded, not an attack on existence.
- *Invisibility is necessary, not sufficient.* `surjunctive-nonsofic-group-exists`
  exhibits surjunctive groups with nontrivial sofic radical: residually finite
  lamps over a residually finite base. So the conditions above cannot be
  promoted to an existence principle. That proof reduces to surjunctive point
  stabilizers of a normal lamp structure, and `G` has no normal subgroups at
  all. By `strict-automaton-tables-present-an-invisible-window-difference`, any
  solution's own product tables must present a nonsofic group. Its decoder
  window must therefore realize a nonsofic configuration, today a one-sided
  compression configuration, and the decoder identity must genuinely use those
  relators.
