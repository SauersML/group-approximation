---
rg: 2
id: simple-amenable-affine-algebras-have-unital-rank-models
kind: claim
title: A simple amenable affine algebra over any field has a unital rank model, in every characteristic
distinct_from:
  invariant-measure-gives-rank-function-in-char-zero: that produces a rank function from an invariant measure on a groupoid and is restricted to characteristic zero; this produces one from algebraic amenability of the ring, over any field, with no groupoid and no measure.
  elek-amenable-algebras-almost-have-fd-representations: that is Elek's imported statement, whose conclusion is stable finiteness via local almost-representations; this is the single-sequence upgrade to a faithful embedding.
---

**ESTABLISHED (unreviewed).** Let `k` be any field and `R` a simple unital affine `k`-algebra that is
amenable in Elek's sense. Then `R` has a **unital rank model** over `k`: there are integers `d_n` and a
unital injective `k`-algebra homomorphism `Φ : R → ∏_ω M_(d_n)(k)` into the rank-metric ultraproduct.
Consequently `R` carries a faithful Sylvester matrix rank function and is stably finite.

**Why this matters for the program.** Rung (Σ) of `kazhdan-elementary-approximation-type-mirrors-ring-type`
needs a unital rank model. `invariant-measure-gives-rank-function-in-char-zero` supplies one only in
characteristic zero, and `invariant-measure-gives-rank-function-any-field` is open and contains Kaplansky
stable finiteness in characteristic `p`. But the Kazhdan groups exist only in characteristic `p`, because
EJZ needs `R` finitely generated as a ring and a field finitely generated as a ring is finite (Artin–Tate).
This claim supplies the missing half by a route that never mentions a measure.

**Credit.** The compression construction and the fact that the rank radical is an ideal are Elek's
(`elek-amenable-algebras-almost-have-fd-representations`). The content added here is that fixing a single
Følner sequence makes the rank a single Sylvester rank function on all of `R` at once, so simplicity gives
an embedding rather than only stable finiteness; Elek's own lower bound has a constant depending on the
finite dimensional subspace.

**Scope.** Amenability is sufficient, never necessary. Exponential growth does not imply non-amenability
(`k[Γ]` is amenable for every amenable `Γ`). A rank model over a fixed `k` is weaker than exact matriciality
over varying finite fields.
