---
rg: 2
id: labbe-wang-shift-crossed-product-is-finitely-presented
kind: claim
title: The crossed-product algebra of Labbé's minimal aperiodic Wang shift over a finite field is finitely presented
distinct_from:
  labbe-shift-derived-full-group-is-finitely-presented: that asks whether the derived topological full group is finitely presented, a group question; this asks whether the coefficient algebra LC(Omega_U, F_q) x| Z^2 is finitely presented, which by quantum rigidity is a question about operator-valued local tilings.
  ledrappier-crossed-product-is-finitely-presented: that settles rigidity for a permutive SFT with a fixed point; this asks for rigidity of a minimal aperiodic self-similar SFT, whose crossed product is simple.
---

**OPEN.** Let `Ω_U` be Labbé's minimal aperiodic Wang shift (`minimal-aperiodic-wang-shift-exists`)
and `q` a prime power. Then `R_U = LC(Ω_U, F_q) ⋊ Z^2` is finitely presented. By
`sft-crossed-product-fp-iff-quantum-rigid`, this is equivalent to `D`-quantum rigidity of `Ω_U`
for some `D`.

**Payoff.** `R_U` is finitely generated and simple, since the action is free and minimal. It has a
unital rank model by Følner truncation, and so no halvable corner. Rigidity would make it a
finitely presented infinite-dimensional simple algebra over a finite field with a faithful rank
function. It would then be the gate (a) instance for
`sofic-fp-simple-kazhdan-group-from-fp-simple-ring`, and `EL_n(R_U)` would be `F_q`-linear sofic
and Kazhdan. Simplicity and the rank model are to be written up. Gates (b) and (c) stay open.

**Refutation.** A non-commuting operator-valued local tiling of Labbé's tiles.

## Attempts

- **Periodic models.** Useless in either direction: `Ω_U` has no finite orbit (peer Theorem A in
  `research/artifacts/fp-simple-amenable-z2-sft-2026-09-12.md`). Classical finite models cannot
  refute rigidity, and none are needed to prove it.
- **Entropy walls: dead.** `Ω_U` is self-similar, so it has zero entropy. For a minimal SFT, a wall
  certificate with a finite side forces positive entropy
  (`research/artifacts/sft-crossed-product-presentation-rigidity-2026-09-13.md`, Proposition 4).
  So `positive-entropy-sft-crossed-products-are-not-fp` does not apply.
- **Infinite walls: open.**
  - A refutation of the two-basis type needs two tilings agreeing on a wall of width `> 2D` that
    separates two infinite regions where they differ.
  - Hierarchical tilings have fault lines, but each known ambiguity is one-sided: a single infinite
    supertile lies on each side, and no pair differing along two parallel faults is known.
  - This is heuristic, not checked for `Ω_U`.
- **Permutive propagation: open.** Ledrappier's rigidity propagates commutation from the row above
  through a group law. Whether Labbé's 19 tiles have a propagation law of this kind (a tile
  determined, and inverted, by two neighbours along some direction) was not checked.
- **Genuinely quantum families: open.** Contextual constraint systems such as the magic square have
  operator solutions with no classical counterpart. So wall rigidity need not imply quantum
  rigidity. Undecidability results for such systems suggest that no general algorithm decides
  rigidity; that is a heuristic and not a proof for this shift.
