---
id: passive-block-involution-codes-ascend
kind: claim
title: A control-involution strict rule pair with a passive block admits strict rules over every larger alphabet
distinct_from:
  strict-rule-pairs-ascend-to-larger-alphabets: that is ascent for an arbitrary strict rule pair; this proves ascent for the control-involution codes with a pointwise-fixed block, the form every classified strict table takes, and reduces the general statement to equivalence with this form.
  equal-label-table-is-strict-at-three-symbols-not-two: that fixes one table x_a = x_b and computes its admissible sizes as exactly n >= 3; this isolates the construction mechanism behind that threshold and shows it ascends by one symbol at a time for every such code.
  strict-rule-pairs-pass-to-product-alphabets: that multiplies the alphabet size by a factor with the tables fixed; this adds one symbol at a time to a passive block, reaching every size above the threshold, not only multiples.
artifacts:
  - research/artifacts/alphabet-ascent-and-binary-descent-2026-09-12.md
---

**ESTABLISHED** by [[passive-block-involution-codes-ascend-proof]].

Fix forward and reverse tables `(T_f, T_r)` over label sets `S`, `M`. Call a rule pair over an
alphabet `A` a **control-involution code** if `mu = nu` and there is a map `g : A -> Sym(A)`, written
`v |-> g_v`, with

- every `g_v` an involution (`g_v o g_v = id`);
- `g_v` depending only on the block of `v` in a fixed partition of `A`;
- the relay rule `mu(x) = g_{x(c_2)}( x(c_1) )` for two distinguished window cells `c_1` (data) and
  `c_2` (control).

A block `Z` of the partition is **passive** if every `g_v` fixes `Z` pointwise.

**Claim.** Let a control-involution code be strict for `(T_f, T_r)` over `A` and have a nonempty passive
block `Z`. Let `A' = A ⊔ {∗}` with `∗` adjoined to `Z`, each `g_v` extended by `g_v(∗) = ∗`, and
`g_∗ = id`. Then the extended code is a control-involution code strict for `(T_f, T_r)` over `A'`, with
passive block `Z ⊔ {∗}`.

**Consequences.**
- The admissible alphabet sizes of `(T_f, T_r)` are upward closed above the first size at which a
  control-involution code with a passive block exists.
- The classified strict tables take this form, so their admissible sizes are upward closed uniformly:
  `x_a = x_b` has `g_P = id` on `P = {0,1}` and `g_Q = (0\,1)` on `Q = A \ P`, with `Q` passive (both
  involutions fix `Q` pointwise); the triple `x_a = x_b = x_a x_b` has `h_0 = id`, `h_1 = (0\,2)`,
  `h_2 = (0\,1)`, `h_w = id` for `w >= 3`, with `{3, 4, ...}` passive. This re-derives the
  `n >= 3` evidence of the Boolean-core artifact from one mechanism.
- **Group level.** Through `surjunctivity-is-axiomatized-by-rectangle-clauses`, a group realizing such a
  table over `k` symbols realizes it over every `n >= k` with the same memories.

**What it does not give.** A copy code `mu = pi_{m0}` is not an involution code but ascends trivially
(defined at every size). A strict pair that is neither a copy code nor a control-involution code with a
passive block is not covered; see [[strict-rule-pairs-ascend-to-larger-alphabets]] for the general
statement and the reduction to this form.
