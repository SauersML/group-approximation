---
rg: 2
id: single-active-tag-lift-collapse-proof
kind: route
title: Split the one active symbol into t phases, then apply the unique-largest-fiber collapse theorem to the collapse of phases
target: single-active-symbol-strict-donor-automata-give-every-size
requires:
  - donor-covering-types-give-nonsurjunctive-size-progressions
---

**Import, verbatim.** This is the theorem of the established claim `collapse-lifts-with-unique-largest-fiber-are-surjective`,
landed on origin in commit `708058c4d36308e730bb6fc7c0b1fcf19c7b608a`, after this worktree was branched. Once both
are in one tree, add it under `requires`.

> Let `G` be any group, `A` and `B` finite alphabets, `r : B -> A` a surjection with fibers `Q_a = r^{-1}(a)`, `τ`
> an injective cellular automaton on `A^G` and `Φ` an injective cellular automaton on `B^G` with
> `r ∘ Φ = τ ∘ r`. Suppose some `a0 ∈ A` has `|Q_{a0}| >= 2` and `|Q_{a0}| > |Q_a|` for every `a != a0`. Then one of
> the following holds: `|Q_{a0}| ∈ NS(G)`; `τ` and `Φ` are both surjective.

**Proof.** Let `τ` be strict and donor-covering on `L^G`, where `L = Z ⊔ {β}` and `|Z| = z >= 1`.

1. **Fix `t >= 2`.** Apply item 1 of the prerequisite, whose construction is written out in
   `donor-type-tag-lift-size-progression-proof`. It gives an injective automaton `Φ` on `C^G` with
   `C = Z ⊔ ({β} × Z/t)`. It also gives the surjection `σ : C -> L` that fixes `Z` and sends `(β, s)` to `β`, and
   `σ ∘ Φ = τ ∘ σ` holds sitewise.
2. **Fibers.** For `ζ ∈ Z`, `σ^(-1)(ζ) = {ζ}`. The fiber `σ^(-1)(β)` has `t >= 2` elements. So `β` is the unique
   largest fiber, of size `t`.
3. **Import.** Take `A = L`, `B = C`, `r = σ`, `a0 = β`, with `τ` and `Φ` injective. The import gives
   `t ∈ NS(G)`, or both `τ` and `Φ` surjective. `τ` is not surjective, so `t ∈ NS(G)`.
4. Since `t >= 2` was arbitrary, every `n >= 2` lies in `NS(G)`.
