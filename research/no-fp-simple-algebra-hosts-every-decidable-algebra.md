---
rg: 2
id: no-fp-simple-algebra-hosts-every-decidable-algebra
kind: claim
title: No class of algebras sharing one recursive word-problem time bound contains every two-generated algebra with solvable word problem
distinct_from:
  complexity-bounded-host-classes-are-not-universal: that is the principle for groups, with a two-generated graph-shift input group; this is the same principle for associative algebras, with monomial inputs, and it covers single finitely presented simple algebras.
artifacts:
  - research/artifacts/bh-algebra-envelopes-2026-09-12.md
---

**ESTABLISHED.** Let `K` be a computable field and let `T : N -> N` be recursive.
Let `H` be a class of finitely generated `K`-algebras. Suppose every `B` in `H`
has, for some finite generating set, a word-problem algorithm running in time
`C_B T(C_B l) + C_B l + C_B` on words of length `l`. Then some two-generated
monomial algebra

```text
A_X = K<x, y> / ( x y^n x : n in X ),     X ⊆ N decidable,
```

has solvable word problem and embeds in no member of `H`.

## Consequences

- **No single universal host.** Every finitely presented simple algebra has
  solvable word problem (`fp-simple-algebras-have-solvable-word-problem`), so it
  has some recursive time bound. Hence no single finitely presented simple
  algebra contains every algebra with solvable word problem.
- **No fixed family of hosts.** A family with one shared recursive bound cannot
  serve as a universal container for `algebra-boone-higman-conjecture`. That
  includes tensor powers of one Leavitt algebra, or Steinberg algebras of one
  finite-type groupoid family with a shared bound. Envelopes must grow in
  complexity with their inputs, exactly as for groups.
