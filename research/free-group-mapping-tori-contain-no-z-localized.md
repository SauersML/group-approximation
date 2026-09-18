---
rg: 2
id: free-group-mapping-tori-contain-no-z-localized
kind: claim
title: An ascending HNN extension of a finitely generated free group along an endomorphism injective on rational homology contains no Z_(l), and in general Z_(l) forces iterates sinking through the lower central series
distinct_from:
  z-localized-fixes-a-vertex-or-end-of-every-tree: that is the general tree lemma; this applies it to mapping tori of free group endomorphisms and adds a lower-central-series count.
  fg-linear-groups-have-roots-at-finitely-many-primes: that excludes linear hosts; mapping tori of free groups are finitely presented and residually finite (Borisov–Sapir) but not linear in general, so this is a separate class.
artifacts:
  - research/artifacts/gq-gq-k2-q-rf-hosts.md
---

**ESTABLISHED (2026-09-18)** through `free-group-mapping-tori-contain-no-z-localized-proof`. Lane proof (gq-k2-q), not
independently reviewed. Inputs: `z-localized-fixes-a-vertex-or-end-of-every-tree`; Nielsen–Schreier; the
Magnus–Witt description of the lower central quotients of free groups. No novelty is claimed.

## Setting

`F` is free of finite rank, `φ : F -> F` is injective, and `G_φ = ⟨F, t | t^(-1) x t = φ(x), x ∈ F⟩`. This is
finitely presented, and residually finite by Borisov–Sapir. `γ_c F` is the lower central series, and
`Φ_c : Γ_c -> Γ_c` is the map induced by `φ` on `Γ_c = γ_c F / γ_(c+1) F`, a free abelian group of finite rank.

## Statement

Let `A ≤ (Q,+)` contain an element divisible by infinitely many primes, for example `A = Z_(l)`.

1. **Reduction.** If `A ≤ G_φ`, then after conjugation `A ≤ ∪_k t^k F t^(-k)`. Moreover there is `x ∈ F ∖ {1}`
   whose *root set* `P(x) = {p prime : φ^k(x) is a p-th power in F for some k}` is infinite.
2. **Non-sinking elements have finite root sets.** Let `x ∈ γ_c F ∖ γ_(c+1) F` with `Φ_c^k [x] ≠ 0` for all `k`.
   Then `P(x)` is finite.
3. **Consequence.** If `A ≤ G_φ`, some `x ≠ 1` sinks: the lower central degree of `φ^k(x)` tends to infinity with
   `k`.
4. **Homologically injective case.** If `φ_ab ⊗ Q` is injective, for instance when `φ` is an automorphism (so
   `G_φ` is free-by-cyclic), then every `Φ_c ⊗ Q` is injective and nothing sinks. So `G_φ` contains no `Z_(l)`, no
   `Z[1/P]` with `P` infinite, and no `Q`.

## Scope

Part 4 covers every free-by-cyclic group and every mapping torus whose endomorphism is injective on `H_1(F;Q)`. The
remaining mapping tori are those whose endomorphism kills some rational homology class. There part 3 is the only
constraint recorded, and whether a sinking element can have an infinite root set is OPEN.
