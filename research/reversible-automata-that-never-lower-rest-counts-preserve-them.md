---
rg: 2
id: reversible-automata-that-never-lower-rest-counts-preserve-them
kind: claim
title: A reversible automaton fixing the rest configuration that never lowers the number of non-rest sites never raises it
distinct_from:
  count-raising-reversible-automata-lower-biased-rokhlin-entropy: that proves a count-raising reversible automaton forces Rokhlin supremum zero on its group; this asserts that no such automaton exists over any group.
  passive-fixing-injective-automata-are-surjective: that proves surjectivity when reserved symbols stay in place; this is the count statement that makes every design moving its star set by a reversible automaton surjective.
  every-injective-ca-has-uniform-single-site-output-law: that asks uniform input to give a uniform one-site law, and is equivalent to surjunctivity; this asks small-bias inputs not to lose non-rest density exactly, for count-monotone automata only, and no equivalence with surjunctivity is known.
---

**OPEN.** Let `G` be a countably infinite group, `A` a finite alphabet, `a ∈ A`, and `ψ` a bijective cellular
automaton on `A^G` with `ψ(a^G) = a^G`. For `x` with finitely many sites outside `a`, write `|x|` for their number.
If `|ψ(x)| >= |x|` for every such `x`, then `|ψ(x)| = |x|` for every such `x`.

Equivalently, with `Φ = ψ^-1`: an injective automaton fixing `a^G` that never raises the count, and restricts to a
bijection of the finitely supported configurations, never lowers it.

**Why it matters.** It is item 6.2 of `notes/gottschalk-surjunctivity-conjecture-frontier-swarm-2026-09-16.md`. Take
`C = A ⊔ {*}` and an injective automaton on `C^G` whose output star set is `ψ(Z)` whenever the input star set is
`Z`, for a bijective `ψ` on `{0,1}^G` fixing all-stars. Injectivity makes `ψ` never lower the non-star count, and
count preservation makes the design surjective (`count-raising-reversible-automata-lower-biased-rokhlin-entropy`,
first consequence). So this claim kills every such design, over every group, as a route to a strict automaton.

**Known cases.**
- **Sofic groups.** They have infinite Rokhlin supremum, so the established theorem forbids a count-raising `ψ`.
- **Any group with a free ergodic action of positive Rokhlin entropy.** Its supremum is positive
  (`positive-rokhlin-entropy-action-gives-positive-supremum`), and the same theorem applies. This gives the route
  `reversible-count-preservation-from-positive-rokhlin-entropy`.
- **Low counts, over every group, binary alphabet.** Counts 1 and 2 are kept (part B of
  `count-raising-reversible-automata-rokhlin-deficit-proof`).
- **Finite groups** are excluded by hypothesis. There the statement holds trivially: summing `|ψ(x)| - |x| >= 0`
  over the finite set `A^G` gives `0`.

## Attempts

- **Induction on the count** (solo follow-up, 2026-09-17). Singletons and pairs split into finitely many near
  translation classes and far ones that `ψ` fixes up to a uniform shift. So an injection that lands among near
  classes is a bijection of them. From count 3 on, a near cluster can map to a far one, the far thresholds grow
  with the count, and the class count is no longer finite. It dies there.
- **Charge expansion.** With binary alphabet, the change `|Φ(Z)| - |Z|` expands as `Σ_{∅ ≠ V ⊆ Z} Γ(V)`, where
  `Γ` is translation invariant and supported on subsets of translates of the memory. A first loss sits at a set
  `V` of size `m >= 3` inside one translate of the memory. That confines the witness but gives no contradiction
  without a measure on the group, and the measure argument needs a positive Rokhlin supremum.
