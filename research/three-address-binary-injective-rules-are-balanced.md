---
rg: 2
id: three-address-binary-injective-rules-are-balanced
kind: claim
title: Over every group, an injective binary automaton with at most three memory elements has a balanced rule
distinct_from:
  surjunctivity-is-axiomatized-by-rectangle-clauses: that records a small-memory exclusion for rule pairs whose encoder and decoder memories both have size two; this excludes unbalanced binary encoders with three memory elements, whatever the decoder, by invisible one- and two-site flips.
  monotone-binary-injective-rules-are-copies: that excludes monotone rules at any memory size through constant backgrounds; this excludes every unbalanced rule at memory size three through the rectangle relation and an involution-glued double flip.
  unbalanced-effective-rule-certifies-strictness: that says an unbalanced effective rule over a forward-sufficient table certifies strictness; this says the certificate needs at least four effective memory elements over F_2.
artifacts:
  - research/artifacts/unbalanced-design-memory-collisions-2026-09-12.md
---

**ESTABLISHED 2026-09-12** by `three-address-binary-injective-rules-are-balanced-proof`.

Let `G` be any group and `tau` an injective automaton on `{0,1}^G` whose memory has at most three
elements. Then its rule is balanced. So every unbalanced injective binary automaton, and every binary
design refuting `unbalanced-forward-tables-identify-memory-letters`, has at least four effective
memory elements.

**Tools** (artifact, Section 2).
- **Rectangle relation.** An unbalanced binary rule is insensitive at every address in some context.
  If the difference sets `D_m = {m^-1 m'}` are pairwise disjoint, a single flip is invisible. So some
  `m_1^-1 m_1' = m_2^-1 m_2'` with `m_1 != m_2`.
- **Three addresses.** With `M = {1, a, b}`, exactly one of `a`, `b`, `a^-1 b` must be an involution.
  Two of them, or a cyclic relation, would make `<a, b>` amenable, hence the automaton bijective. The
  insensitive contexts must also project to complementary symbols at the glued site.
- **Double flip.** Normalize to `a^2 = 1`, `Ins_1 ⊆ {x_a = 1}` and `Ins_a ⊆ {x_1 = 0}`. The rule
  takes the form `mu(x_1, 0, x_b) = x_1 + f(x_b)` and `mu(1, 1, x_b) = f(x_b)`. Flipping sites `1` and
  `a` together from `(0,0)` to `(1,1)` changes neither glued block. The two other blocks reading
  them have private contexts and can be made insensitive.
