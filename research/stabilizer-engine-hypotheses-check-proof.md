---
rg: 2
id: stabilizer-engine-hypotheses-check-proof
kind: route
title: Check free-factor isotropy, germ faithfulness and local transitivity by 3-cycles for the base vertex of the stabilizer engine, then apply the germ-cocycle retraction
target: stabilizer-engines-force-fp-vertex-groups
requires:
  - free-factor-isotropy-of-fp-full-subgroups-is-fp
---

Notation is as in the target. The facts about `X` used below are read off the
definitions in `free-product-boundary-groupoids-carry-the-vertex-group-homology`, and
each one is checked here.

**0. The space.**
- `X` is compact, Hausdorff and totally disconnected. It is the closure of the rays in
  the product, over the countable edge set, of two-point sets.
- `D` acts on `X` by homeomorphisms, because it permutes the half-trees.
- Elements of `F` are exactly the homeomorphisms that are piecewise-`D` on a finite clopen
  partition, by compactness.
- `X` has a basis of clopen sets.

**1. (H1) `D_v = B`.** In the Bass–Serre tree the stabilizer of the vertex `dB` is
`dBd^{-1}`. So `D_v = B` for `v = 1B`, and `B` fixes no other point of `X`.

**2. (H2) Germ faithfulness.**
- The edges at `v` are the edges `c ∈ B`. With `H` the half-tree of the edge `1` on the
  `A`-side, `X = {v} ⊔ ⊔_{c ∈ B} cH`, which is (i) of the setting together with
  `X = H ⊔ K`.
- The basic neighbourhoods of `v` are `N_{F_0} = {v} ⊔ ⊔_{c ∈ B \ F_0} cH`, with `F_0 ⊂ B`
  finite.
- `b ∈ B` maps `cH` onto `bcH`. If `b ≠ 1`, then for any `c ∉ F_0` the nonempty set `cH`
  lies in `N_{F_0}` and is carried onto the disjoint set `bcH`. So `b` is not the identity
  on any neighbourhood of `v`.

**3. (H3) Local motion of `v` by elements of `D(F)`.**
- **Target points.** Fix `a ∈ A \ 1`, which exists since `k >= 2`. Let `N` be a
  neighbourhood of `v`, and choose `F_0` with `N_{F_0} ⊂ N`. For `c ∈ B \ F_0`, the vertex
  `y_c = c a v` lies in `cH`, since `a K ⊂ H` by (ii) and `v ∈ K`. So `y_c ∈ N_{F_0}`.
- **Distinctness.** The points `y_c` are pairwise distinct and differ from `v`:
  `caB = c'aB` forces `a^{-1} c^{-1} c' a ∈ B`, so `c = c'` by normal forms.
- **Choosing a small clopen set.** Take `c ≠ c'` in `B \ F_0`, and put `d = ca`,
  `d' = c'a`. Choose pairwise disjoint open sets `O_0 ∋ v`, `O_1 ∋ dv`, `O_2 ∋ d'v`
  inside `N_{F_0}`. Then choose a clopen `U ∋ v` with
  `U ⊂ O_0 ∩ d^{-1} O_1 ∩ d'^{-1} O_2`. So `U`, `dU` and `d'U` are pairwise disjoint
  and lie in `N`.
- **Two involutions.** Let `τ` be `d` on `U`, `d^{-1}` on `dU`, and the identity
  elsewhere. Let `τ'` be the same with `d'`. Both are involutions in `F`.
- **The 3-cycle.** Put `γ = [τ, τ'] = τ τ' τ τ'`, with the rightmost map applied first.
  It lies in `D(F) ≤ E`, and it is the identity outside `U ∪ dU ∪ d'U ⊂ N`. Tracking
  `v`: `v ↦ d'v ↦ d'v ↦ v ↦ dv`. So `γ(v) = dv = y_c`.
- **Infinitely many points.** `c` ranges over the infinite set `B \ F_0` (take `c'` to be
  any other element), so infinitely many points `γ(v)` arise.

**4. Conclusions.**
1. Any such `E` is a finitely presented group of piecewise-`D` homeomorphisms that
   contains `B` and satisfies (H3). Steps 1–2 give (H1) and (H2). The imported theorem
   `free-factor-isotropy-of-fp-full-subgroups-is-fp` applies with `x = v` and shows that
   `B` is finitely presented.
2. Take `E = F`.
3. `D(F)` is normal in `F`, so `E = D(F)·B` is a subgroup. `E / D(F) ≅ B / (B ∩ D(F))`
   embeds in the abelian group `F / D(F)`. It is a quotient of the finitely generated
   group `B`, so it is a finitely generated abelian group, hence finitely presented. An
   extension of a finitely presented group by a finitely presented group is finitely
   presented (P. Hall). So `E` is finitely presented, and (1) applies.
4. If `B` is perfect, then `B = [B, B] ≤ [F, F] = D(F)`. So every `E` between `D(F)` and
   `F` contains `B`, and (1) applies. `∎`
