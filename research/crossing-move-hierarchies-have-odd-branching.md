---
rg: 2
id: crossing-move-hierarchies-have-odd-branching
kind: claim
title: In a one-head move hierarchy with bounded junctions and slowly growing domains, crossings split into an odd number of sub-crossings, and a binary hierarchy must mix crossings with returns
distinct_from:
  smart-induced-on-genuine-moves-has-exact-tripling: that is SMART's exact ternary hierarchy; this explains why a crossing-only hierarchy cannot be binary.
  bs12-embeds-in-brin-thompson-2v: that is the open BS(1,2) question; this is a structural constraint on one route to it (a binary SMART).
artifacts:
  - research/artifacts/gq-gq-nv-obstruct-binary-smart-search.md
---

**ESTABLISHED (2026-09-18)** through `crossing-move-hierarchies-have-odd-branching-proof`.
Elementary lane proof (gq-nv-obstruct). Not independently reviewed.

**Setting.** Take a moving-tape system in which the head moves at most one cell per step, and a
*move hierarchy* for it:
- for each level `k`, a set of *moves*, which are finite orbit segments, each with a *domain*: an
  interval of `d(k)` cells;
- every level-`(k+1)` move is the concatenation of its sub-moves, which are level-`k` moves with domains
  inside the parent's, with at most `B` steps between consecutive sub-moves and at most `B` steps before
  the first and after the last;
- `d(k+1) - d(k) <= c`, and `d(k) → ∞`.

A move is a **crossing** if it starts within `w` cells of one end of its domain and ends within `w` cells
of the other end. It is a **return** if it starts and ends within `w` cells of the same end. Here
`c`, `B` and `w` do not depend on `k`.

**Statement.** Let `k` satisfy `d(k) > 2(c + B + w) + 2`.
1. A level-`(k+1)` crossing has an odd number of sub-moves that are crossings. A level-`(k+1)` return has
   an even number.
2. So if every move is a crossing, every branching number is odd. SMART, whose moves are all crossings
   (Callard–Salo `prop:smart-moves`), branches by 3.
3. So a hierarchy with branching exactly 2 needs return moves. Each crossing then splits as
   (crossing, return) or (return, crossing), and each return as (crossing, crossing) or (return, return).

**Consequence for `BS(1,2)` via a binary SMART.** A one-head machine with exact binary timing and
bounded junctions has to realize returns.
- The prefix-consistent choice is the Jacobsthal scheme `C→ ↦ C→ R_R`, `R_R ↦ C← C→` (and mirrors).
- Its returns turn one cell short of the domain end.
- That turn has to be triggered by marks written near the head, as SMART's `0|1` and `0|2` marks are.
- The exhaustive searches in the artifact found no machine doing this in the searched classes. Every
  binary counter found has an exact binary skeleton plus an unbounded linear walk.
