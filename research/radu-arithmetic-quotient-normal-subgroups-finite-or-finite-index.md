---
rg: 2
id: radu-arithmetic-quotient-normal-subgroups-finite-or-finite-index
kind: claim
title: Every normal subgroup of Radu's arithmetic quotient Q is finite or of finite index
distinct_from:
  radu-horizontal-quotient-is-arithmetic-lattice: that identifies Q as a cocompact irreducible arithmetic lattice in PGL_2(Q_2) x PGL_2(Q_2); this is the normal subgroup theorem for that lattice.
  radu-arithmetic-quotient-is-flexibly-permutation-stable: that asks for Hamming stability of almost actions of Q; this is the purely algebraic normal subgroup property.
---

**OPEN (import not yet pinned at source).**  `Q` of `radu-horizontal-quotient-is-arithmetic-lattice`
is an irreducible cocompact `S`-arithmetic lattice in `PGL_2(Q_2) × PGL_2(Q_2)`, of total rank 2.
The claim is the normal subgroup theorem for `Q`: every normal subgroup of `Q` is finite or has
finite index. Since `Q` is not amenable, it follows that every amenable quotient of `Q` is finite,
so `ρ(N)` has finite index for every `N ◁ Γ_R` with `Γ_R/N` amenable.

Expected sources, to be read before this becomes ESTABLISHED:
* Margulis's normal subgroup theorem for irreducible lattices in products of simple algebraic
  groups over local fields of total rank at least 2 (Margulis, *Discrete Subgroups of Semisimple
  Lie Groups*, Chapter IV; the exact theorem number and its hypotheses on the center and on
  `S`-arithmeticity are not checked here);
* or the Bader–Shalom normal subgroup theorem for irreducible cocompact lattices in products of
  just non-compact locally compact groups (Invent. Math. 2006; arXiv id not located in this lane).

Checks still needed: irreducibility in the sense the theorem requires, and triviality of finite
normal subgroups of `Q` (as a subgroup of a center-free group).
