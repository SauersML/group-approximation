---
rg: 2
id: invariant-measure-gives-rank-function-in-char-zero
kind: claim
title: In characteristic zero an invariant probability measure on the unit space gives a faithful Sylvester matrix rank function on the Steinberg algebra, so the algebraic Tarski chain becomes an equivalence
distinct_from:
  cantor-z-crossed-product-embeds-in-continuous-factor: that is Ara-Claramunt for Cantor Z-systems over an arbitrary field, obtained by a Bratteli-diagram rank completion; this covers every minimal effective ample groupoid but only over subfields of the complex numbers, by the groupoid von Neumann algebra.
  invariant-measure-gives-rank-function-any-field: that is the open statement over an arbitrary field, which contains Kaplansky stable finiteness; this is its settled characteristic-zero case.
  char-zero-steinberg-stably-finite-iff-invariant-measure: that obtains stable finiteness of the Steinberg algebra in characteristic zero through the reduced C*-algebra and the Tarski paradox side; this constructs a faithful Sylvester matrix rank function, strictly stronger than stable finiteness, through the groupoid von Neumann algebra.
artifacts:
  - research/artifacts/un-algebraic-tarski-2026-09-13.md
---

**ESTABLISHED** (unreviewed; proof route `invariant-measure-gives-rank-function-in-char-zero-proof`).

Let `𝒢` be a minimal, effective, Hausdorff, ample, second countable groupoid with compact unit space
`X`, let `μ` be a `𝒢`-invariant Borel probability measure on `X`, and let `k ⊆ ℂ` be a countable
subfield. Then `A_k(𝒢)` carries a faithful Sylvester matrix rank function `rk` with
`rk(1_U) = μ(U)` for every compact open `U ⊆ X`. In particular `A_k(𝒢)` is stably finite.

**Consequence.** Combined with `algebraic-tarski-for-steinberg-algebras`, all four conditions become
equivalent for such `𝒢` and every countable field `k` of characteristic zero (each embeds in `ℂ`):

  faithful Sylvester matrix rank function ⟺ stably finite ⟺ `θ` completely non-paradoxical
  ⟺ an invariant probability measure exists.

**The tension this exposes.** The equivalence is available exactly where property (T) is not.
Ershov–Jaikin-Zapirain (`elementary-groups-over-fg-rings-have-property-t`) needs `R` finitely
generated **as a ring**, and a field that is finitely generated as a ring is finite (Artin–Tate). So
`A_k(𝒢)` is a finitely generated ring only when `k` is finite, and the EJZ route to Kazhdan elementary
groups runs only in positive characteristic. Characteristic zero has the exact dichotomy and no
Kazhdan groups; characteristic `p` has the Kazhdan groups and an open arrow. The Kazhdan simple groups
of this program therefore live precisely where the equivalence is unavailable, so each measure-branch
example must be witnessed by hand. That is what the Pestov 9.1 answer does with its return-word tower
embedding, and what Ara-Claramunt do for all Cantor `Z`-systems.
