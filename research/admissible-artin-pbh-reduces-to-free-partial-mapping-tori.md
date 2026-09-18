---
rg: 2
id: admissible-artin-pbh-reduces-to-free-partial-mapping-tori
kind: claim
title: An admissibly oriented Artin group A *_C B (C of index 2 in B) has an index-two twisted double of A, which embeds in the HNN extension of the free group A that twists the single subgroup C by an automorphism
distinct_from:
  admissibly-oriented-artin-groups-satisfy-boone-higman: that reduces this class to the open decidable-edge HNN permanence in general; this reduces it to one explicit kind of group, the HNN extension A *_(α : C -> C) of a free group whose domain and range are the same finitely generated subgroup.
  admissibly-oriented-artin-groups-split-over-free-groups: that is Jankiewicz's splitting A *_C B; this is what the index-2 edge inclusion C ≤ B does to it.
  domain-exact-hnn-hosts-have-multivalley-kernels: that confines kernels of maps from HNN extensions to domain-exact hosts; the HNN extension here has domain equal to range, of infinite index in A, so no host with finite-index edge groups is domain-exact for it.
  pbh-class-closed-under-relative-holomorphs: that covers ascending HNN extensions along partial conjugations; the HNN extension here is not ascending (its edge group C is a proper subgroup of A).
---

**ESTABLISHED** (lane proof, in the body; not independently reviewed). No priority is claimed.

## Statement

Let `G = A *_C B` with `A, B, C` free of finite rank, `C ≤ B` of index 2 (so `C ⊴ B`), and `C ≤ A`. Fix `y ∈ B \ C` and let `α ∈ Aut(C)` be `α(c) = y^-1 c y`. Put `H_α = A *_(α : C -> C) = < A, t | t c t^-1 = α(c), c ∈ C >`.

1. `K = ker(G -> B/C)` (with `A ↦ 0`) has index 2 in `G`, and `K = A *_C (y A y^-1)`, a **twisted double** of `A`: two copies of `A` glued along `C`, by the identity on the first and by `α` on the second.
2. `K` embeds in `H_α`, via `A ↦ A` and `y a y^-1 ↦ t^-1 a t`.
3. Hence `G ∈ B_A` whenever `H_α ∈ B_A` (`B_A` is closed under subgroups and finite-index overgroups, `boone-higman-type-a-class-closed-under-finite-extensions`).
4. **Free-factor case.** If `C` is a free factor of `A`, say `A = C * E`, then `H_α = (C ⋊_α Z) * E ∈ B_A`.

**Application.** By Jankiewicz (arXiv:2006.04717v2, Theorem 4.3 and Corollary 4.13, as imported in `admissibly-oriented-artin-groups-split-over-free-groups`), every Artin group with an admissible partial orientation that is not bipartite with all labels even has this form, with `rk A = |E(Γ)|` and `rk C = 1 - 2|V(Γ)| + 4|E(Γ)|`. For a large-type triangle `(M, N, P)`, `M, N, P >= 3`: `A ≅ F_3`, `C ≅ F_7`. So **every large-type triangle Artin group lies in `B_A` as soon as the corresponding HNN extension `F_3 *_(α : F_7 -> F_7)` does.** Since `rk C > rk A` there, `C` is never a free factor of `A`, and part 4 does not apply directly; what is open is `B_A` for these specific HNN extensions.

## Proof

1. `G -> Z/2`, `A ↦ 0`, `B -> B/C`, is well defined (both are trivial on `C`); `K` is its kernel. On the Bass--Serre tree of `G`, `K` has two orbits of `A`-type vertices (`A`, `yA`), one orbit of `B`-type vertices with stabilizer `K ∩ B = C`, and two orbits of edges (`C`, `yC`), both with stabilizer `C` (as `yCy^-1 = C`). The quotient is the path `A — C — y A y^-1` with middle vertex group equal to both edge groups, so `K = A *_C (yAy^-1)`, where `C ≤ yAy^-1` is `y C y^-1 = C`. Identifying `yAy^-1` with a copy of `A` by `a ↦ y a y^-1`, the element `c ∈ C` corresponds to `y^-1 c y = α(c)` in the copy.
2. In `H_α`, by Britton's lemma `t^-1 a t ∈ A` iff `a ∈ α(C) = C`, so `A ∩ t^-1 A t = t^-1 C t = C`. The vertices `A` and `t^-1 A` of the Bass--Serre tree of `H_α` are adjacent, with edge stabilizer `C`, so `< A, t^-1 A t > = A *_C t^-1 A t` (two adjacent vertex stabilizers of a tree generate their amalgam over the edge stabilizer). The map of step 2 sends the gluing `c = y α(c) y^-1` of step 1 to `c = t^-1 α(c) t`, which holds since `t c t^-1 = α(c)`. It is the identity on the first copy and an isomorphism onto `t^-1 A t` on the second, compatible with the gluings, so it is an isomorphism `K -> < A, t^-1 A t >`.
3. Immediate.
4. `H_α = < C, E, t | t c t^-1 = α(c) > = (C ⋊_α Z) * E`. A free-by-cyclic group `F_n ⋊_α Z` lies in `B_A`: `F_n ⋊ Aut(F_n)` embeds in `Aut(F_(n+1)) = Aut(F_n * <z>)` (`w ∈ F_n` acts as `z ↦ z w`, `φ ∈ Aut(F_n)` acts on `F_n` and fixes `z`; the conjugation rule matches), so `F_n ⋊_α Z` embeds in `Aut(F_(n+1))` if `α` has infinite order in `Aut(F_n)`, and in `(F_n ⋊ Z/k) × Z ≤ Aut(F_(n+1)) × Z` if `α` has order `k`. `Aut(F_(n+1)) ∈ B_A` (`aut-free-groups-satisfy-permutational-boone-higman`); `B_A` is closed under direct products, subgroups (`boone-higman-type-a-class-closed-under-finite-extensions`) and free products (BFFHZ Corollary F, in the same Aut(F_n) node). ∎

## What would finish the large triangles

A proof that `F_3 *_(α : F_7 -> F_7)` lies in `B_A` for Jankiewicz's `α`. Two possible lines:
- **Virtual free factors.** By M. Hall's theorem `C` is a free factor of some finite-index `A_1 ≤ A`; if a finite-index subgroup of `H_α` can be chosen whose graph of groups has every edge group a free factor of both adjacent vertex groups (a clean graph of free groups), the pieces become free-by-cyclic groups and free products, and the remaining question is closure of `B_A` under HNN extensions of free groups over free factors.
- **Hosts.** A host HNN extension that is exact on one side cannot have finite-index edge groups here (`domain-exact-hnn-hosts-have-multivalley-kernels`, Use), so a host would have to keep infinite-index edges.
