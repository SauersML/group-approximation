---
rg: 2
id: kazhdan-finiteness-in-nv-via-cnd-transversal
kind: route
title: A cnd function proper modulo the triangular subgroup already makes every Kazhdan subgroup of nV finite
target: kazhdan-subgroups-of-brin-thompson-groups-are-finite
requires:
  - brin-thompson-nv-cnd-proper-modulo-triangular-subgroup
  - thompson-v-has-haagerup-property
---

Lane gq-nv-obstruct, 2026-09-17. Not independently reviewed.

**Point.** The transversal half `ψ_1` of the Haagerup split
(`brin-thompson-nv-a-t-menable-via-triangular-split`) is not a weak relative of
the Haagerup property. With no fibre half, it already gives the finiteness of all
Kazhdan subgroups of `nV`. Consequently it answers Zaremsky 2.19(a), (c) and (d)
with "no", through `some-hyperbolic-group-in-no-nv-via-kazhdan-finiteness` and
`some-gl-n-z-in-no-nv-via-kazhdan-finiteness`. The trick is to apply `ψ_1` after
the coordinate-permutation automorphisms of `nV`.

**n = 1.** `V` has the Haagerup property (`thompson-v-has-haagerup-property`,
Farley), and a group with both (T) and the Haagerup property is finite.

**n >= 2.** Let `K <= nV` have property (T).
1. *Automorphisms.* For a permutation `σ` of `{1,…,n}`, let `σ` also denote the
   coordinate permutation of `C^n`. Conjugating a map that is canonical on a brick
   `∏ u_i C → ∏ v_i C` by `σ` gives a map canonical on the permuted bricks. So
   `α_σ(g) = σ g σ^-1` is an automorphism of `nV`. It carries `T_n` to
   `T_n^σ = σ T_n σ^-1`: the elements that, together with their inverses, map
   fibres of the projection to the coordinates `σ(1), …, σ(i)` into fibres, for
   every `i < n`.
2. *Covering.* Fix `σ`. The group `K' = σ^-1 K σ <= nV` has (T), so the cnd
   function `ψ_1|_{K'}` is bounded. That holds because (T) implies (FH), by the
   Delorme–Guichardet theorem (Bekka–de la Harpe–Valette, *Kazhdan's Property
   (T)*, Chapter 2). So `K' ⊆ {ψ_1 <= R} ⊆ g_1T_n ∪ ⋯ ∪ g_rT_n`.
   - If `k ∈ K' ∩ g_iT_n`, then `K' ∩ g_iT_n = k(K' ∩ T_n)`.
   - So `[K' : K' ∩ T_n] <= r`.
   - Conjugating back gives `[K : K ∩ T_n^σ] < ∞`.
3. *Intersection.* For each `j`, pick `σ_j` with `σ_j(1) = j`. An element of
   `T_n^{σ_j}` maps fibres of `x ↦ x_j` into fibres, so its `j`-th coordinate
   depends only on `x_j`: `g(x)_j = h_j(x_j)`.
   - `h_j` is bijective, because `g^-1` has the same form.
   - On a brick where `g` is canonical, `h_j` is a prefix replacement.
   - So `h_j ∈ V`, and `⋂_j T_n^{σ_j} = V^n`.
   - The reverse inclusion is clear: `V^n` lies in every `T_n^σ`.

   Hence `K ∩ V^n = ⋂_j (K ∩ T_n^{σ_j})` has finite index in `K`.
4. *Finish.*
   - `V^n` has the Haagerup property: if `ψ_V` is a proper cnd function on `V`,
     then `(h_1,…,h_n) ↦ Σ ψ_V(h_i)` is a proper cnd function on `V^n`.
   - `K ∩ V^n` has (T), being of finite index in `K`.
   - So `K ∩ V^n` is finite, and therefore `K` is finite. ∎

**Byproduct.** `ψ_1' = Σ_j ψ_1 ∘ α_{σ_j}^{-1}` is a cnd function on `nV`, since
a cnd function composed with an automorphism is cnd, and so is a sum. Each of its
sublevel sets lies in finitely many cosets of every `T_n^{σ_j}`. A finite union
of cosets of `A` intersected with a finite union of cosets of `B` is a finite
union of cosets of `A ∩ B`. So the sublevel sets lie in finitely many cosets of
`V^n`: **`ψ_1` exists if and only if a cnd function proper modulo `V^n`
exists**. The converse holds because `V^n <= T_n`.

**Refutation test.** A subset `X ⊆ nV` has *relative property (T)* when every
cnd function on `nV` is bounded on `X`. If some such `X` lies in no finite union
of left cosets of `V^n`, then `ψ_1` does not exist. For example, `X` could be
an infinite Kazhdan subgroup, or the normal `Z^2` of a copy of `Z^2 ⋊ F`,
`F <= SL_2(Z)` non-amenable, placed off every finite union of cosets of `V^n`.
Such an `X` would also show that `nV` fails the Haagerup property (Zaremsky 2.7).
