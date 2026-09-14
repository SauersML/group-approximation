---
rg: 2
id: injective-automata-fixing-passive-sites-are-surjective
kind: claim
title: An injective automaton that leaves every site carrying a passive symbol unchanged is surjective, over every group
distinct_from:
  passive-fixing-injective-automata-are-surjective: that assumes in addition that the automaton never writes a passive symbol at an active site; this drops that hypothesis, which the finite invariant pieces never need.
  local-passivity-preserving-injective-automata-are-surjective: that allows passivity defined by neighbourhood patterns and needs a no-creation condition; this is its sitewise case, where the no-creation condition is automatic.
artifacts:
  - research/artifacts/ideas-gottschalk-3-2026-09-14.md
---

**ESTABLISHED** through `passive-site-fixing-surjectivity-via-local-passivity` (elementary; no novelty claimed).

**Statement.** Let `G` be a group, `C` a finite alphabet and `P ⊆ C` a nonempty set of passive symbols. Let `Φ`
be an injective cellular automaton on `C^G` such that `Φ(x)(g) = x(g)` whenever `x(g) ∈ P`. Then `Φ` is surjective.

**What it sharpens.** `passive-fixing-injective-automata-are-surjective` assumes in addition that `Φ` never writes
a passive symbol at an active site, and its proof node says both hypotheses are needed. They are needed for its
finite pieces, not for the theorem. With pieces "equal to `x₀` off `E`, active set inside `E`", passive fixing
alone keeps each piece invariant (`local-passivity-surjectivity-proof`, step 2).

**Consequences.**
- **Ascent and descent through reserved symbols.** A strict automaton on `(A ⊔ D)^G` must, on some configuration,
  rewrite a site carrying a `D`-symbol. Designs that keep reserved symbols in place fail whatever they write at
  ordinary sites, including designs that erase ordinary symbols into reserved ones.
- **Binary codings over `G × F`.** A binary strict automaton over `G × F` that leaves the two constant fibres
  `0^F`, `1^F` in place is surjective once it is injective. It must rewrite a constant fibre on some
  configuration; making non-constant fibres constant is no substitute.
