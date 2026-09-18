---
rg: 2
id: euclidean-artin-toric-commensurability
kind: claim
title: A Euclidean Artin group lies in B_A if and only if the fundamental group of the toric Weyl arrangement complement of its finite root system does, for any invariant lattice between coroots and coweights
distinct_from:
  affine-artin-groups-satisfy-k-pi-1-conjecture: that is asphericity of the orbit space; this is a commensurability statement between the Artin group and a toric arrangement group, used to transfer membership in B_A.
  b-tilde-artin-complement-fibres-over-configuration-space: that is the Li--Roushon space chain for type B̃_n, including the passage to (C^×)^n by the exponential map; this is the same first step for every Euclidean type, stated as a B_A equivalence.
  fiber-type-toric-arrangement-groups-lie-in-the-pbh-class: that is the Boone--Higman consequence for fiber-type toric arrangements; this identifies which toric arrangement a Euclidean Artin group corresponds to.
artifacts:
  - research/artifacts/gq-bh-bh-verify-artin-euclidean-toric.md
---

**ESTABLISHED** through `euclidean-artin-toric-commensurability-proof`. This is a lane
proof, elementary given the classical identification of Euclidean Artin groups with
orbit-space fundamental groups, and not independently reviewed. No priority is
claimed; the exponential passage to toric complements is standard.

**Setting.**
- Let `W̃ = W ⋉ Q^∨` be an irreducible Euclidean Weyl group of rank `n`, with finite
  root system `Φ ⊂ V* = (R^n)*` and coroot lattice `Q^∨`.
- Let `M = V_C − ∪_(α ∈ Φ, k ∈ Z) {α = k}`, and `A(X̃_n)` the Euclidean Artin group.
- Let `L` be a `W`-invariant lattice with `Q^∨ ⊆ L ⊆ P^∨`, where
  `P^∨ = {u : α(u) ∈ Z for all α ∈ Φ}` is the coweight lattice.
- Put `T_L = V_C / L = Hom(L*, C^×)` and let
  `M_L = T_L − ∪_(α ∈ Φ^+) {t : t^α = 1}` be the toric Weyl arrangement complement.

**Statement.**
1. `M/L ≅ M_L`, and `π_1(M/Q^∨)` is a subgroup of index `|W|` in `A(X̃_n)` and of
   index `[L : Q^∨]` in `π_1(M_L)`.
2. Hence `A(X̃_n) ∈ B_A` if and only if `π_1(M_L) ∈ B_A`, for any one (equivalently,
   every) such `L`.
3. **Consequences.**
   - `A(C̃_n) ∈ B_A` for every `n`, because the C_n toric arrangement is fiber-type
     (`fiber-type-toric-arrangement-groups-lie-in-the-pbh-class`).
   - The same argument works for the A_n toric arrangement (configurations in `C^×`,
     via Fadell--Neuwirth). This gives `A(Ã_n) ∈ B_A`, which BFFHZ Corollary B already
     gives.
   - Both are known. The point is a uniform mechanism.

**What it reduces the open cases to.** D̃_n (n >= 4), Ẽ_6, Ẽ_7, Ẽ_8 and F̃_4 lie in
`B_A` if and only if the toric Weyl arrangement complements of D_n, E_6, E_7, E_8 and
F_4 have fundamental groups in `B_A`. For D_n with `L = Z^n` this is the explicit
space `N_D = {v ∈ (C^×)^n : v_i ≠ v_j and v_i v_j ≠ 1 for i ≠ j}`. These arrangements
are not fiber-type (`weyl-toric-arrangements-b-d-e-f-are-not-fiber-type`), so they
need a different mechanism.
