---
rg: 2
id: ballistic-machine-runs-give-periodic-points
kind: claim
title: A moving-head machine with a ballistic run over a constant background has a periodic point, so no inducing of it has a renormalization of any height
distinct_from:
  odometer-factor-witnesses-mix-coordinates: that shows a witness of an odometer factor has no periodic points; this gives a local, table-level test that produces periodic points.
  crossing-move-hierarchies-have-odd-branching: that constrains the branching of move hierarchies; this constrains the rules of the machine, independently of any hierarchy.
  smart-type-machines-branch-by-every-odd-number: that family M_m has ballistic rules, so this lemma excludes it as a base; SMART and SMART_m have none.
---

**ESTABLISHED** through `ballistic-machine-runs-give-periodic-points-proof`. Elementary lane proof, not reviewed.
No priority is claimed; this is folklore-level for aperiodic Turing machines.

**Setting.** `M` is a moving-head machine: finitely many states, each with a direction, and a finite alphabet `Σ`.
In phase 2 the head moves one cell in its direction. In phase 1 it reads, writes, and changes state; the new state
carries the new direction. `F` is its moving-tape map on the space of configurations (tape relative to the head,
state, phase).

**Definition.** A state `q` runs **ballistically** over a symbol `a` if the run started in `q`, at phase 2, with
the tape ahead of the head equal to `a^∞`, never reverses direction. A single rule `(q, a) → (b, q)` that keeps the
state, and so the direction, is enough.

**Statement.** If some state runs ballistically over some symbol, then:
1. `F` has a periodic point;
2. `F` factors onto no infinite odometer `Z_m` with `π ∘ F = π + 1`;
3. for every clopen `Y` that every `F`-orbit meets within bounded time, the first-return map `S = F_Y` has a
   periodic point, so `S` has no height-`m` renormalization for any `m ≥ 2`
   (`renormalizable-thompson-elements-are-odometer-codes`). In particular no such `S` is a base for
   `renormalizable-thompson-elements-give-baumslag-solitar`.

**Consequences.**
- `M_m` of `smart-type-machines-branch-by-every-odd-number` has the ballistic rules `F_j → (0, F, pass)` (over `j`)
  and `H0 → (2j, H, pass)` (over `0`). So **no inducing of `M_m` is a renormalization base**, which settles the
  correction on that node.
- The 21 "clean" quadrupling tables of `research/artifacts/gq-affq-even-branching-search.md` contain `F0 → F0`, so
  they are excluded too.
- SMART and `SMART_m` pass: every state reverses direction within two steps on every constant background.

**Lesson for general BH.** A BS(1,m) witness built from a machine needs a hierarchy that covers every
configuration. The cheapest necessary condition is that every state **turns on every constant background**; a
single ballistic rule leaves a domain-wall periodic point that no inducing can remove. As a table-level filter it
comes before periodicity checks and timing searches. It explains in one line why sweeping designs, including my
`M_m` and the quadrupling tables, can pass counts and random-tape tests and still fail globally.
