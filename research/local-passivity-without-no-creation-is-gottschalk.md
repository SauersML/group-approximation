---
rg: 2
id: local-passivity-without-no-creation-is-gottschalk
kind: claim
title: Dropping the no-creation hypothesis from the local passivity theorem is equivalent to surjunctivity, already for one rest pattern
distinct_from:
  local-passivity-preserving-injective-automata-are-surjective: that proves surjectivity under fixing passive sites and creating no active site, and leaves open whether the second hypothesis can be dropped when the neighbourhood has more than one site; this answers that the first hypothesis alone holds for every constant-fixing automaton whose memory lies in the neighbourhood, so dropping the second is the conjecture itself, while the second alone suffices for a single rest pattern.
  injective-automata-fixing-passive-sites-are-surjective: that is the one-site neighbourhood, where fixing passive sites already creates none; this is the gap that opens as soon as the neighbourhood contains the memory.
  gottschalk-surjunctivity-conjecture: that is the conjecture; this shows that one natural strengthening of the passivity barrier is equivalent to it, group by group.
---

**ESTABLISHED** by `local-passivity-without-no-creation-is-gottschalk-proof` (elementary; no novelty claimed for the
method).

Notation of `local-passivity-preserving-injective-automata-are-surjective`: `W ∋ 1` is finite, `P ⊆ A^W` contains a
constant pattern `a^W`, `Act(x) = { g : (g⁻¹x)|_W ∉ P }`, and for an automaton `Φ` on `A^G`:
1. **(fixes passive sites)** `Φ(x)(g) = x(g)` for every `g ∉ Act(x)`;
2. **(creates no active site)** `Act(Φ(x)) ⊆ Act(x)`.

**Theorem.** Let `G` be a group.
- **A. Hypothesis (1) alone is the conjecture.** The following are equivalent.
  - `G` is surjunctive.
  - For every finite alphabet `A`, `a ∈ A`, finite `W ∋ 1` and `P = {a^W}`, every injective automaton on `A^G`
    satisfying (1) is surjective.

  More precisely: if `τ` is injective and not surjective on `A^G`, some power `τ^k` fixes `a^G`, is injective and
  not surjective, and satisfies (1) for `P = {a^W}` whenever `W ⊇ M_k ∪ {1}`, with `M_k` a memory of `τ^k`.
- **B. Hypothesis (2) alone suffices for one rest pattern.** If `P = {a^W}`, hypothesis (2) implies (1). So an
  injective automaton on `A^G` such that `Φ(x) = a` on `gW` whenever `x = a` on `gW` is surjective, over every group.
- **C. Hypothesis (2) alone for general `P` is again the conjecture.** Take `P = A^W`. Then `Act(x) = ∅` for every
  `x`, so (2) always holds.

**What this settles.** The node `local-passivity-preserving-injective-automata-are-surjective` records as open
whether (2) can be dropped when `|W| > 1`. By A, it can be dropped for every `(W, P)` over `G` exactly when `G` is
surjunctive. So no proof of that strengthening exists that does not prove the conjecture, and a counterexample to
it is the same thing as a strict automaton.

**The boundary, stated for rest patches.** Fix a rest symbol `a` and a finite `W ∋ 1`, and call `gW` a rest patch of
`x` when `x = a` on `gW`.
- "The centre of every rest patch stays at rest" holds for every automaton fixing `a^G` with memory inside `W`, so
  surjectivity under it is the conjecture.
- "Every rest patch stays at rest" forces surjectivity over every group. It still lets the automaton write non-rest
  symbols at rest sites, but only at sites none of whose `W`-patches is a rest patch. Those sites lie in
  `{x ≠ a} W⁻¹`, within one patch of the non-rest region.

**Forced property of a minimal counterexample.** A strict automaton, after passing to a power fixing `a^G`, has memory
`M` and satisfies (1) for `W = M ∪ {1}`, `P = {a^W}`. By B, on some configuration `x` it must write a non-rest symbol
inside a `W`-shaped rest patch of `x`. It must do so for every finite `W ∋ 1`, not only for `W ⊇ M`.
