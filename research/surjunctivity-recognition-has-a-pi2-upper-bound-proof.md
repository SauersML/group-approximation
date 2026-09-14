---
rg: 2
id: surjunctivity-recognition-has-a-pi2-upper-bound-proof
kind: route
title: Choose words for the rectangle labels and split the clause into derivations and non-derivations
target: surjunctivity-recognition-has-a-pi2-upper-bound
requires:
  - surjunctivity-is-axiomatized-by-rectangle-clauses
artifacts:
  - research/artifacts/gottschalk-rectangle-clauses-and-recognition-2026-09-12.md
---

Section 3 of the artifact.

- `K` fails `rho_D` iff some labelling satisfies its premises and violates every
  conclusion.
- A labelling of a presented group is a choice of words.
- A word equation holds in `K` iff it has a finite derivation from `R`; with `R`
  recursively enumerable these derivations can be enumerated, so the premises are
  `Sigma^0_1` and the violated conclusions `Pi^0_1`.
- Strict data form a decidable set. The existential quantifier over data and words
  gives `Sigma^0_2` for non-surjunctivity.
- With a total decider for the word problem, both brackets are decidable and the
  bound drops to `Sigma^0_1`.
