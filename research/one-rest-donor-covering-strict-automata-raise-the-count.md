---
rg: 2
id: one-rest-donor-covering-strict-automata-raise-the-count
kind: claim
title: A strict donor-covering automaton with a single rest symbol strictly raises the number of active sites on some finite configuration
distinct_from:
  finite-injective-positive-charge-automata-are-surjective: that proves surjectivity for injective automata conserving a positive charge; this applies it to donor-covering automata, where relays make the active count never drop, and reads off that strictness forces a strict rise.
  count-raising-reversible-automata-lower-biased-rokhlin-entropy: that forces Rokhlin supremum zero from a bijective count-raising automaton; this concerns non-surjective automata, for which no entropy consequence of a rise is known.
  reversible-automata-that-never-lower-rest-counts-preserve-them: that asks whether bijective automata never lowering the count keep it; this proves that a non-surjective injective donor-covering automaton with one rest symbol cannot keep it.
  local-passivity-preserving-injective-automata-are-surjective: that kills injective designs creating no active site and fixing passive sites; this kills injective donor-covering designs with one rest symbol that keep the active count, even when active sites move.
---

**ESTABLISHED** by `one-rest-donor-covering-count-proof`. Elementary given the charge theorem.

Notation as in `donor-covering-strict-automata-descend-to-two-symbols`, with `L = {0} ⊔ B`. For `ℓ` with finitely
many active sites write `|ℓ|` for their number. Let `τ` be an injective donor-covering automaton on `L^G`, over any
group `G`. Then:
1. `τ(0^G) = 0^G`, and `τ` maps configurations with finitely many active sites to such configurations;
2. `|τ(ℓ)| >= |ℓ|` for every such `ℓ`;
3. if `τ` is not surjective, then `|τ(ℓ)| > |ℓ|` for some such `ℓ`.

**Consequence.** Item 4 of `donor-covering-strict-automata-descend-to-two-symbols` asks, for type `(1, b)`, for an
injective automaton that eats rest sites into active ones on some finite configuration and never loses an active
site without a relay: a Hilbert-hotel mechanism. Over sofic groups no strict automaton exists at all. The copying
rule on the tree with a fixed end has this shape, doubling the count, but it lives off groups.
