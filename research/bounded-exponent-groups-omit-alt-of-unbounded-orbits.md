---
rg: 2
id: bounded-exponent-groups-omit-alt-of-unbounded-orbits
kind: claim
title: A bounded-exponent group of Cantor homeomorphisms contains alt(H,X) only for H with bounded orbits, so Nekrashevych's periodic groups, all topological full groups of infinite groups and the golden-mean group F have unbounded exponent
distinct_from:
  some-fp-simple-group-has-an-infinite-bounded-exponent-subgroup: that is the open separator P_n; this kills one class of candidate witnesses, the periodic groups produced by the full-group mechanism, and leaves P_n open.
  full-shift-topological-full-group-is-residually-finite: that excludes subgroups of one full group by residual finiteness; this excludes, for every action, the full and alternating groups themselves and every group containing them, with no residual finiteness.
  almost-automorphism-torsion-subgroups-are-rf: that excludes all torsion subgroups of almost automorphism groups by residual finiteness; this excludes alternating full groups of arbitrary actions, which are not residually finite, by counting disjoint translates.
  nekrashevych-golden-mean-fragmentation-group-properties: that is the literature import (periodicity, growth, full-group equality, amenability); this derives unbounded exponent from it and records what a bounded-exponent witness inside F would have to be.
  bishop-schesler-branch-hosts-act-on-no-regular-rooted-tree: that shows one family of branch groups contains Alt(m) for unboundedly many m; this shows it for every alternating full group of an action with unbounded orbits.
---

**ESTABLISHED** by `bounded-exponent-groups-omit-alt-of-unbounded-orbits-proof` (lane proof,
w13-bh-follow, elementary apart from the import `nekrashevych-golden-mean-fragmentation-group-properties`;
not independently reviewed). No priority claimed; parts (A)–(C) are folklore-level.

## Statement

Let `X` be a Cantor set, `H` a group acting on `X` by homeomorphisms, and `full(H,X)`, `alt(H,X)` as in
Nekrashevych (imported definitions).

- **(A) Unbounded orbits give every finite group.** If `sup_x |Hx| = ∞`, then `alt(H,X)` contains a copy
  of `Alt_n` and `full(H,X)` contains a copy of `Sym_n`, for every `n`. So both contain every finite group
  and have unbounded exponent.
- **(B) Bounded orbits force finiteness.** If `H` is finitely generated, acts faithfully and
  `sup_x |Hx| < ∞`, then `H` is finite. So (A) applies to every infinite finitely generated group acting
  faithfully on `X`.
- **(C) The kill.** Let `E ≤ Homeo(X)` have exponent `N`. If `alt(H,X) ≤ E`, then every `H`-orbit has at
  most `N+1` points. Hence:
  - an infinite finitely generated group `E ≤ Homeo(X)` of bounded exponent satisfies `E ≠ full(E,X)`;
  - such an `E` contains `alt(H,X)` for no infinite finitely generated `H` acting faithfully on `X`.
- **(D) The golden-mean group.** Nekrashevych's golden-mean group `F` and its simple derived subgroup
  `[F,F]` contain `Alt_n` for every `n`. So neither has bounded exponent, and neither is a witness for
  `some-fp-simple-group-has-an-infinite-bounded-exponent-subgroup`.
- **(E) What a witness inside `F` would be.** Every finitely generated subgroup of `F` is amenable and has
  subexponential growth. So an infinite finitely generated bounded-exponent subgroup of `F` would be an
  infinite amenable bounded-exponent group of subexponential growth. The source records that no infinite
  finitely generated bounded-exponent group known in 2016 was amenable. The same amenability holds in
  every fragmentation of a minimal dihedral action.

## What this kills

The approach class is: take the bounded-exponent witness to be a periodic group produced by the full-group
mechanism. Its members are:
- the simple periodic groups `alt(G,X)` of Nekrashevych's fragmentation theorem;
- topological full groups of infinite finitely generated actions;
- the golden-mean `F` and `[F,F]`;
- any group that contains one of these.

- **Invariant:** the largest size of a family of pairwise disjoint `H`-translates of a clopen set.
- **Where every member dies:** at `n` disjoint translates, the definition of `alt` itself puts `Alt_n`
  inside, and `Alt_n` has an element of order at least `n-1`.

This settles the open follow-up posted by w12-bh-break: "exponent of Nekrashevych's F (bounded exponent
would settle some-fp-simple-group-has-an-infinite-bounded-exponent-subgroup)". The exponent is unbounded.

After (C), the full-group periodicity mechanism is exhausted for `P_n`. Its only remaining use is
through subgroups of a fragmentation that are not themselves full or alternating. By (E), any such
witness would be an amenable Burnside-type group.

## Not covered

- Fragmentation groups `G` that contain no `alt(H,X)` with unbounded orbits. They are covered only by the
  amenability barrier (E).
- Other subgroups of the finitely presented simple host that contains `F`. That host is the twisted
  Brin–Thompson group of the full contracting RSG constructed by w12-bh-break. There (E) says nothing
  outside `F`.
- Bounded-exponent groups acting on `X` whose rigid stabilizers are small: this node says nothing about
  them.
