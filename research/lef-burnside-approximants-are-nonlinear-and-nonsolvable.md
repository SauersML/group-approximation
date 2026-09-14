---
rg: 2
id: lef-burnside-approximants-are-nonlinear-and-nonsolvable
kind: claim
title: Finite approximants of an infinite LEF group of bounded exponent are eventually non-nilpotent, of unbounded derived length, and of unbounded linear degree
distinct_from:
  finite-nilpotent-groups-satisfy-local-restricted-burnside: that proves the local principle for finite nilpotent groups; this adds the solvable and bounded-degree linear cases for approximants of an infinite LEF group
  local-restricted-burnside-iff-lef-burnside-groups-are-finite: that shows infinite LEF groups of exponent N exist exactly when the local principle fails; this constrains the finite groups that approximate such a group
  finitely-generated-linear-groups-are-residually-finite: that is Malcev's theorem for one linear group; this applies it to ultraproduct limits of bounded-degree approximants
---

**ESTABLISHED** through `lef-burnside-approximants-nonlinear-nonsolvable-proof`.

**Setting.** Let `m, N >= 2`, and let `(L, s)` be an infinite `m`-generated group
of exponent dividing `N`. Let `(Q_n, s^(n))` be finite marked groups converging to
`(L, s)` in the space of marked groups: for each `r`, for all large `n`, the words
of length `<= r` trivial in `Q_n` are exactly those trivial in `L`. By
`local-restricted-burnside-iff-lef-burnside-groups-are-finite` such a sequence
exists iff `L` is LEF, and it exists for some `L` iff `LRB(m,N)` fails.

**Statement.**
0. **Laws transfer.** If a law `ω(y_1, ..., y_j) = 1` holds in infinitely many
   `Q_n`, it holds in `L`.
1. `|Q_n| -> ∞`.
2. **Nilpotent.** Only finitely many `Q_n` are nilpotent.
3. **Solvable.** For every `ℓ`, only finitely many `Q_n` are solvable of derived
   length `<= ℓ`.
4. **Linear.** For every `d`, only finitely many `Q_n` have a faithful linear
   representation of dimension `<= d` over a field (the fields may vary with `n`).

So a refutation of `LRB(m,N)` at every radius needs finite groups that are
eventually non-nilpotent, of unbounded derived length, and without faithful
representations of any bounded dimension over any field.

**Remark (heuristic, not used).** By the Jordan-type structure theorems for
finite linear groups (Larsen--Pink; not pinned here), clause 4 points to
approximants involving alternating groups of unbounded degree or groups of Lie
type of unbounded rank.
