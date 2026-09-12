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
- *Linear decoders.* Dead for even `|H|` over `F_2`, whatever the encoder, by
  `invariant-output-automata-have-only-nonlinear-decoders`. The degree-one part
  of the decoder identity would be a one-sided inverse with augmentation zero.
- *Route through a Hilbert-hotel orbit.* The equivariant self-surjections of
  `G/Gamma` for the infranormal Kazhdan subgroup of the nine-leaf configuration,
  and the Cantor boundary orbit of Thompson's `V`, have infinite stabilizers. By
  `full-shift-maps-to-infinite-stabilizer-coset-shifts-are-constant`, no
  continuous equivariant map from the full shift into those coset shifts is
  nonconstant, so this route is dead. The codomain must be a finite-stabilizer
  coset shift, which is exactly the invariant-output form.
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
- *Table filter (2026-09-12).* By `strict-pairs-transfer-to-table-realizations`,
  every homomorphism from the window's table group into a finite group, or into
  any group already proved surjunctive, must kill `x_h`. The table group has
  relators from `S x M` and `H x M`. So candidate windows can be screened on unit
  products alone, before any rule is tried.
- *No quotient-ring route (2026-09-12).* By
  `full-shift-maps-into-two-sided-algebraic-subshifts-are-constant`, the Leavitt
  kernel subshift receives only the zero automaton from full shifts. So the
  coset-invariant output cannot be produced by passing through the dual of the
  Leavitt algebra, or of any other quotient of `F_2[G]`.
- *The host is not excluded (2026-09-12).* By
  `gottschalk-counterexamples-lie-outside-the-permanence-closure`, `G` lies outside
  the closure of the sofic groups under every surjunctivity permanence theorem now
  available. So no positive method in the graph rules this claim out.
- *Global signature (2026-09-12).* By
  `positive-rokhlin-entropy-makes-leavitt-units-surjunctive`, a solution would
  force every free ergodic p.m.p. action of `G` to have zero Rokhlin entropy,
  Bernoulli shifts included. So `G` would fail Seward's POS. That excludes no
  finite window by itself, but it names the entropy statement a certificate
  refutes as a byproduct.
- *Small ball windows are dead (2026-09-12).*
  `small-leavitt-invariant-output-windows-have-finite-separations` runs the table
  filter on 45 ball windows:
  - Thompson units, low-depth transvections, the GL(4,2) atlas charts, the
    nine-leaf `E_ij(1)` with compressors, and the full nine-leaf window with all 30
    `E_ij(r)`;
  - radii up to `2:2`, and `h` of order 2 or 3.

  In every window a finite image of the table group keeps `x_h != 1`:
  - a character to `Z/2` or `Z/3`;
  - a permutation image of degree at most 7, PSL(3,2) for the nine-leaf `E_ij(1)` windows;
  - for the full nine-leaf window, an image onto GL(4,2).

  The full window survives every nilpotent image, and no finite ring realizes its
  Leavitt products `t_k s_m = delta_km`. The GL(4,2) image uses block elementary
  matrices over `M_2(F_2)` whose coefficients depend on the position, and it realizes
  those products in a rank-one corner. So a certificate needs memories outside these
  balls. A candidate window's table group must also kill `x_h` under such
  position-dependent corner representations, not only in small simple groups.
