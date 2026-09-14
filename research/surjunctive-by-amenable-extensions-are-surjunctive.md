---
rg: 2
id: surjunctive-by-amenable-extensions-are-surjunctive
kind: claim
title: A group with a surjunctive normal subgroup and amenable quotient is surjunctive
distinct_from:
  sofic-kernel-amenable-quotient-permanence: that is permanence of soficity, proved with finite models of the kernel; this asks the same permanence for surjunctivity, where the kernel may be nonsofic and has no finite models.
  products-with-a-sofic-factor-are-surjunctive: that concerns direct products with a sofic factor; this concerns extensions with amenable quotient, twisted ones and ascending HNN extensions included, where the kernel is the non-sofic side.
  gottschalk-surjunctivity-conjecture: that is the universal statement; this is one permanence consequence of it, which would reach ascending HNN extensions of Kun--Thom-type groups that no operation of the permanence closure covers.
artifacts:
  - research/artifacts/amenable-extension-surjunctivity-transfer-2026-09-12.md
---

**OPEN.** Let `N` be a normal subgroup of `G` with `N` surjunctive and `G/N` amenable. Then `G` is surjunctive.

**Why it matters.** Ascending HNN extensions `N *_phi` of a surjunctive `N` are `(surjunctive)`-by-`Z`. When the
directed union of copies of `N` is not residually finite, no operation of the permanence closure `S*` applies.
The finite-index case is `surjunctivity-is-a-commensurability-invariant`.

## Attempts

- **Coset transplant (artifact Section 2).** An automaton over `G`, restricted to a finite union of `N`-cosets
  indexed by `F <= G/N`, is an automaton over `N` with alphabet `A^(F M)`. The decoder recovers the input only on
  the interior `F^- = {q : q S <= F}`, and a Garden of Eden pattern of the image forbids a pattern on a positive
  fraction of disjoint tiles of `F`. Surjunctivity of `N` then gives a contradiction exactly when the boundary loss
  `|F \ F^-|` is zero. That is Theorem A: decoder memory inside `N` forces surjectivity, over any quotient.
- **Where it dies.** With a decoder that reads across cosets, the transplant maps the full shift over `N` into a
  product of `n` proper subshifts and a full track that is `|F \ F^-|` symbols larger. Plain surjunctivity of `N`
  does not forbid such a map. A deficit that grows with `n` is needed.
  - For an amenable quotient, the deficit must be linear in `n`.
  - For a two-ended quotient, `|F \ F^-|` is bounded, so any deficit that tends to infinity is enough.
- **Conditional transfer (artifact Section 3).** `amenable-extensions-of-uqs-groups-are-surjunctive` pays the boundary
  with a deficit uniform over tracks missing different patterns. Over two-ended quotients an asymptotic deficit
  suffices, which covers ascending HNN extensions. The missing input is
  `surjunctive-groups-are-uniformly-quantitatively-surjunctive`, and it is not known for any nonsofic group.
- **Characteristic-zero linearization (artifact Section 1.3).** It gives no access. The complex linearization of
  a strict automaton is a non-normal endomorphism of `C[Z/q wr G]`, and trace or rank arguments see only
  `tau_* lambda << lambda`.
