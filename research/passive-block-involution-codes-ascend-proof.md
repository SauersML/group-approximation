---
rg: 2
id: passive-block-involution-codes-ascend-proof
kind: route
title: Adjoining a symbol to a passive block preserves strictness of a control-involution code
target: passive-block-involution-codes-ascend
requires: []
artifacts:
  - research/artifacts/alphabet-ascent-and-binary-descent-2026-09-12.md
  - research/artifacts/w3-vf-positive-verification-2026-09-12.md
---

Let `(mu, nu)`, `mu = nu`, be a control-involution code strict for `(T_f, T_r)` over `A`: relay rule
`g_{x(c)}(x(1))` with data at label `1`, involutions `g_v` depending only on the block of `v`, and a
nonempty passive block `Z` fixed pointwise by every `g_v`. Put `A' = A ⊔ {∗}`, adjoin `∗` to `Z`, extend
`g_v(∗) = ∗` for `v in A`, and set `g_∗ = g_Z`.

**The extension is a control-involution code with passive block `Z ⊔ {∗}`.** Each extended `g_v` is an
involution: unchanged on `A`, fixing `∗`. `g_∗ = g_Z` agrees with `g_z` for every `z in Z`, so `g` still
depends only on blocks. Every `g_v` fixes `Z` pointwise by hypothesis and fixes `∗` by construction.

**A retraction intertwines the rules.** Fix `z_0 in Z` and let `phi : A' -> A` be the identity on `A`
with `phi(∗) = z_0`. For all `v, d in A'`,

    phi( g_v(d) ) = g_{phi(v)}( phi(d) ).

- `v in A`, `d in A`: both sides are `g_v(d)`.
- `v in A`, `d = ∗`: the left side is `phi(∗) = z_0`; the right side is `g_v(z_0) = z_0`, since `Z` is
  passive.
- `v = ∗`: `g_∗ = g_Z = g_{z_0}` and `phi(∗) = z_0`, reducing to the case `v = z_0`.

So `phi(mu'(w)) = mu(phi o w)` for every window `w` over `A'`, and likewise for `nu`.

**Decoder identity on `T_f`.** Let `p'` be an `A'`-assignment consistent with `T_f`. Then `phi o p'` is
an `A`-assignment consistent with `T_f`, since a sitewise map preserves equalities. By intertwining,
`phi( C'(p') ) = C( phi o p' ) = phi( p'(1,1) )`, using the decoder identity over `A` for `C`, the forward
composite. The data path has length two: the sink reads relay `1`, which reads cell `(1,1)`, so

    C'(p') = g_u( g_v( p'(1,1) ) )

for two control values `u, v in A'`. Every extended involution preserves `A` and fixes `∗`, so
`C'(p') = ∗` iff `p'(1,1) = ∗`. If both are `∗` they agree. Otherwise both lie in `A`, where `phi` is
injective, so `C'(p') = p'(1,1)`.

**Reverse identity fails on `T_r`.** Strictness over `A` gives an `A`-assignment consistent with `T_r` on
which the reverse composite differs from the demanded symbol. It is also an `A'`-assignment. On windows
with symbols in `A` the extended rules equal the old ones, so the composite is unchanged and the failure
persists.

So the extended code is strict for `(T_f, T_r)` over `A'`. Iterating adds any number of passive symbols,
so `(T_f, T_r)` admits strict rules over every alphabet of size `>= |A|`. QED.

**Instances.** For `x_a = x_b` at `A = {0,1,2}` the passive block is `{2}` with `g_Q = (0\,1)`, so every
adjoined symbol gets `g_∗ = (0\,1)`; growing the block gives every `n >= 3`, matching the verified
threshold of `equal-label-table-is-strict-at-three-symbols-not-two`. For `x_a = x_b = x_a x_b` the passive
block `{3,4,...}` is nonempty from `n = 4` with `g_∗ = id`, and the `n = 3` base is the separate
construction of Example 6.4 of the Boolean-core artifact.

**Verification.** `w3-vf-positive`: PASS after correction (Section 9 of
`research/artifacts/w3-vf-positive-verification-2026-09-12.md`). The conclusion and the coverage are
unchanged, but the proof as first landed had two gaps:
- **The rule `g_∗ = id`.** It breaks block dependence when the passive block acts nontrivially, as `Q`
  does in the `x_a = x_b` instance.
- **The decoder step.** Deleting identity factors does not yield an `A`-equation.

Corrected rule: `g_∗ = g_Z`, with every involution fixing `∗`. The proof then runs through the retraction
`A' -> A` that sends `∗` into `Z` and intertwines the relay rules, with data cell `c_1 = 1`. **Applied** by
lane w3-alphabet in the landing after df4e1151c4: the text above is the corrected proof, and the claim now
states the data-at-label-`1` hypothesis and the rule `g_∗ = g_Z`.
