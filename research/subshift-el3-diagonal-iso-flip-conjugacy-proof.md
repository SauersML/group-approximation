---
rg: 2
id: subshift-el3-diagonal-iso-flip-conjugacy-proof
kind: route
title: Points from maximal normal subgroups of the diagonal, full groups from its normalizer, flip conjugacy from Giordano–Putnam–Skau
target: subshift-elementary-group-diagonal-iso-gives-flip-conjugacy
requires:
  - locally-constant-simple-group-normal-subgroups-are-open-sets
  - subshift-elementary-group-rigid-supports-are-mutual-centralizers
  - topological-full-groups-determine-flip-conjugacy
artifacts:
  - research/artifacts/sk-rigidity-intrinsic-reconstruction-2026-09-13-part1.md
---

Derivation (artifact §4).

**From α to a homeomorphism.** Let `α: G_X → G_Y` with `α(L_X) = L_Y`.
- `GL_3(F_2)` is simple nonabelian, so `α|_(L_X)` is induced by a homeomorphism `h: X → Y`
  (`locally-constant-simple-group-normal-subgroups-are-open-sets`).
- `α(N_(G_X)(L_X)) = N_(G_Y)(L_Y)`. The induced actions on points are compatible
  (`subshift-elementary-group-rigid-supports-are-mutual-centralizers`, item 5), so `h Γ_X h^(-1) = Γ_Y`.

**Piecewise closure.** For `Γ ≤ Homeo(X)`, let `P(Γ)` be the set of homeomorphisms that agree with elements of `Γ` on
the pieces of a finite clopen partition. It is defined from the action alone, so `h P(Γ_X) h^(-1) = P(Γ_Y)`.

`P(Γ_X) = [[T]]`:
- `⊆` because `Γ_X ≤ [[T]]`.
- `⊇`: given `x` and `n ≠ 0`, choose clopen `V ∋ x` with `V, T^nV, T^(2n)V` pairwise disjoint (no periodic points).
- The swaps `τ_1: V ↔ T^nV` and `τ_2: V ↔ T^(2n)V`, by the corresponding powers of `T`, lie in `[[T]]`.
- On the three levels they are the transpositions `(01)` and `(02)`. So `[τ_1,τ_2]` is the 3-cycle `0→1→2→0`, an
  element of `[[T]]' ≤ Γ_X` that equals `T^n` on `V`.
- Every element of `[[T]]` is locally a power of `T`, so it lies in `P(Γ_X)`.

So `h[[T]]h^(-1) = [[S]]`, the groups `[[T]]` and `[[S]]` are isomorphic, and
`topological-full-groups-determine-flip-conjugacy` gives flip conjugacy.

**Converse.** A homeomorphism `ψ` with `ψT = S^ε ψ`, `ε = ±1`, gives the ring isomorphism
`f u^j ↦ (f∘ψ^(-1)) u^(εj)`. It maps `LC(X,F_2)` onto `LC(Y,F_2)`, so `EL_3` of it maps `L_X` onto `L_Y`.
