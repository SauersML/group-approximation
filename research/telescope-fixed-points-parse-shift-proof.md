---
rg: 2
id: telescope-fixed-points-parse-shift-proof
kind: route
title: Proof that the self-simulation equation has the unique solution θ_s, a finite-state map singular exactly on the parse shift plus copies of Sing(s), carrying the seed in every germ over the parse shift
target: telescope-fixed-points-are-singular-on-a-parse-shift
requires:
  - telescopic-germ-bases-in-v-germ-extensions-are-v-separated
---

Notation as on the claim. `U = (0^+1)^* 1`.

**Prefix code and parse shift.**
- `U` is a prefix code. A word in `U` is a sequence of blocks `0^{n_i}1` with `n_i ≥ 1`, followed by
  one block `1` (`n = 0`), and the first occurrence of a block with `n = 0` ends the word. So no
  word of `U` is a proper prefix of another.
- A point `w` has no prefix in `U` iff its block decomposition `0^{n_1}1 0^{n_2}1 ⋯` has every
  `n_i ≥ 1`, possibly ending in `0^ω`. That is the same as `w_0 = 0` and no factor `11`, which
  defines `Y`.
- `C = Y ⊔ ⨆_{u ∈ U} uC`, and `Y` is closed because its complement is a union of cones. `Y` is
  perfect and uncountable: between consecutive 1s one may insert any number `≥ 1` of 0s.

**Item 1.**
- *Existence.* Define `θ_s(uw) = u s(w)` for `u ∈ U`, and `θ_s = id` on `Y`. This is a bijection,
  since `s` is a bijection on each cone `uC` and the cones partition `C ∖ Y`.
- *Continuity* holds off `Y` because the cones are clopen. At `y ∈ Y`, take `m` and the cylinder
  `y|_m C`. No prefix of `y|_m` lies in `U`, so every `x ∈ y|_m C ∖ Y` has its `U`-prefix `u`
  extending `y|_m`. Hence `θ_s` preserves `y|_m C`. The same argument applies to `θ_s^{-1} = θ_{s^{-1}}`.
- *It solves the equation.*
  - For `w = 1w'` the prefix is `u = 1`, so `θ_s(1w') = 1 s(w')`.
  - For `w = 0^n 1 w'` with `n ≥ 1`, the `U`-prefix of `w` is `0^n 1 u'`, where `u'` is the
    `U`-prefix of `w'`, or `w'` lies in `Y` and then so does `w`. So `θ_s(0^n 1 w') = 0^n 1 θ_s(w')`.
- *Uniqueness.* Let `θ` be any solution.
  - By induction on the number of blocks, `θ(uw) = u s(w)` for every `u ∈ U`. For `u = 1` this is
    the seed clause. For `u = 0^n 1 u'` the deeper clause reduces it to `u'`.
  - On `Y` both solutions are determined by continuity, because `Y` is nowhere dense: it is closed
    and contains no cone. So `θ = θ_s`.
- *Homomorphism.* `θ_s θ_t (uw) = u s t(w)`, and `θ_{st} = id` on `Y`. Injectivity: `θ_s = id` forces
  `s = id` on `1C`, hence `s = id`.

**Item 2.** Read `w` left to right.
- State `B` (block start): on `1`, output `1` and hand the rest to `s`. On `0`, output `0` and move to `I`.
- State `I` (inside a block): on `0`, output `0` and stay. On `1`, output `1` and return to `B`.
- An element of `V` is itself a finite asynchronous transducer, so the composite is finite-state.
  The rational group is closed under composition and inverses, and contains `V`.

**Item 3.**
- *Off `Y`.* On the clopen cone `uC`, `θ_s` is `u`-conjugate to `s`, so its singular points there are
  `u·Sing(s)`.
- *On `Y`, with `s ≠ id`.* Let `y ∈ Y` and suppose `θ_s` agreed near `y` with a prefix replacement
  `g`, say on `y|_m C`.
  - `g` fixes `y`, and fixes the perfect set `Y ∩ y|_m C` pointwise, because `θ_s` does.
  - A prefix replacement that fixes a point of a cone and is defined on the whole cone is, on a
    smaller cone around `y`, either the identity or a nontrivial zoom `vx ↦ v'x` with `|v| ≠ |v'|`.
    The second is only possible when `y` is eventually periodic.
  - A nontrivial zoom fixes only `y` in a small cone, so it cannot fix the perfect set `Y` there.
    So `g = id` near `y`.
  - But `θ_s ≠ id` on every cone `uC` with `u` extending `y|_m`, and these cones exist because `y|_m`
    extends to words of `U`: append `11`. This is a contradiction.

**Item 4.** `germ_y(θ_s θ_t) = germ_y(θ_s) germ_y(θ_t)`. If `germ_y(θ_s)` is trivial, then `θ_s = id` on
some `y|_m C`. That forces `s = id` on `1C`-copies inside it, hence `s = id`.

**Item 5.** For `s ∈ V`, `θ_s` is given by a finite transducer. Its graph is recognized by a
synchronous ω-automaton after padding, the standard encoding of rational maps. That is the
hypothesis of bh-free-32's cap. The cap node treats ω-automatic bijections of Cantor space with
arbitrary addresses. Only its finite-parameter special case is used here.
