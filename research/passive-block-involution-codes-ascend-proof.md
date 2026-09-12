---
id: passive-block-involution-codes-ascend-proof
kind: route
title: Adjoining a symbol to a passive block preserves strictness of a control-involution code
target: passive-block-involution-codes-ascend
requires: []
artifacts:
  - research/artifacts/alphabet-ascent-and-binary-descent-2026-09-12.md
  - research/artifacts/w3-vf-positive-verification-2026-09-12.md
---

Let `(mu, nu)`, `mu = nu`, be a control-involution code strict for `(T_f, T_r)` over `A`, with
involutions `g_v` (`v` in `A`) depending only on a partition block of `v`, and a nonempty passive block
`Z` fixed pointwise by every `g_v`. Put `A' = A ⊔ {∗}`, adjoin `∗` to `Z`, set `g_v(∗) = ∗` for every
`v in A`, and `g_∗ = id`. Each extended `g_v` is still an involution of `A'` (it fixes `∗` and is
unchanged on `A`), and `g_∗ = id` is an involution; the partition of `A'` is the old one with `Z`
enlarged to `Z ⊔ {∗}`, so `g'_v` depends only on the block of `v` and `Z ⊔ {∗}` is passive. So the
extension is again a control-involution code.

**Decoder identity on `T_f`.** The decoder identity is a finite conjunction of equations, one per
window assignment `x` consistent with a coincidence of `T_f`, of the form

    (word in the g's, applied to the demanded data symbol) = (demanded data symbol),

where the word's control arguments are the control symbols of `x`. Over `A` this holds for every `x`.
Take any assignment `x'` over `A'`.

- If every control symbol of `x'` lies in `A`, the word is a word in the `g_v` with `v in A`. Evaluate
  it at the demanded data symbol `d`. If `d in A`, all intermediate values stay in `A` (each `g_v`
  preserves `A`), so the equation is the corresponding `A`-equation and holds. If `d = ∗`, every `g_v`
  fixes `∗`, so the word acts as the identity and returns `∗`.
- If some control symbol of `x'` is `∗`, the factor it indexes is `g_∗ = id`; deleting identity factors
  leaves a word whose controls are in `A`, handled by the previous case.

So the decoder identity holds over `A'`.

**Reverse identity fails on `T_r`.** Strictness over `A` gives a reverse assignment over `A` on which
the reverse composite differs from the demanded symbol. The same assignment is a reverse assignment over
`A'` (its symbols lie in `A ⊂ A'`), and the reverse composite is computed by the same word in the
`g_v`, `v in A`, acting on symbols of `A`, so it takes the same value it took over `A`. Hence it still
differs from the demanded symbol, and the reverse identity fails over `A'`.

Therefore the extended code is strict for `(T_f, T_r)` over `A'`. Iterating adds any number of passive
symbols, so `(T_f, T_r)` admits strict rules over every alphabet of size `>= |A|`. QED.

**Instances.** For `x_a = x_b` at `A = {0,1,2}` the passive block is `{2}`; growing it gives every
`n >= 3`, matching the verified threshold of `equal-label-table-is-strict-at-three-symbols-not-two`.
For `x_a = x_b = x_a x_b` the passive block `{3,4,...}` is nonempty from `n = 4`, and the `n = 3` base is
the separate construction of Example 6.4 of the Boolean-core artifact.

**Verification.** `w3-vf-positive`: PASS after correction (Section 9 of
`research/artifacts/w3-vf-positive-verification-2026-09-12.md`). The conclusion and the coverage are
unchanged, but the proof as written has two gaps:
- **The rule `g_∗ = id`.** It breaks block dependence when the passive block acts nontrivially, as `Q`
  does in the `x_a = x_b` instance.
- **The decoder step.** Deleting identity factors does not yield an `A`-equation.

Corrected rule: `g_∗ = g_Z`, with every involution fixing `∗`. The proof then runs through the retraction
`A' -> A` that sends `∗` into `Z` and intertwines the relay rules, with data cell `c_1 = 1`.
