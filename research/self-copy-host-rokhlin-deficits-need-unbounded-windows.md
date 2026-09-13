---
rg: 2
id: self-copy-host-rokhlin-deficits-need-unbounded-windows
kind: claim
title: On groups with zero-or-infinite Rokhlin supremum one Bernoulli deficit forces collapse through arbitrarily large windows
distinct_from:
  rokhlin-supremum-dichotomy-with-centralized-self-copies: that proves the Rokhlin supremum of self-copy groups is zero or infinite; this turns the zero side into finitary collapse and adds that collapsing configurations need unboundedly many reads.
  leavitt-units-have-zero-rokhlin-entropy-supremum: that asserts the zero side for the binary Leavitt unit group; this is a theorem about what any deficit on such a group already forces.
artifacts:
  - research/artifacts/rokhlin-window-localization-and-read-bound-2026-09-12.md
---

Let `G` be countably infinite with `h^Rok_sup(G) ∈ {0, ∞}`. This holds, for example, when `G`
contains `G × G` and finite subgroups of unbounded order, as for the binary Leavitt unit group and
Thompson's `V`. Suppose some configuration over `G` has `Phi < log q` (in the sense of
`bernoulli-rokhlin-deficit-has-a-finitary-witness`). Then:

1. `h^Rok_sup(G) = 0`, so every uniform Bernoulli shift over `G` has Rokhlin entropy `0`;
2. for every alphabet size `q' >= 2` and every `ε > 0` some configuration at `q'` has `Phi < ε`;
3. for every integer `n >= 1`, any configuration at `q'` with `Phi < log q'/n` has more than `n`
   codewords reading the site, so window size `|E| > n`, and code entropy `H(psi)/k < log q'/n`
   (`bernoulli-witness-information-is-bounded-by-code-reads`).

So a single deficit on such a host, for instance the one a strict automaton over the binary
Leavitt unit group would force, already implies collapse at every alphabet, through windows of
unbounded size whose difference subgroups are not Rokhlin-maximal
(`bernoulli-deficit-windows-need-a-non-maximal-difference-subgroup`). Section 3 of the artifact.

**ESTABLISHED 2026-09-12** by [[self-copy-deficit-unbounded-window-proof]].
