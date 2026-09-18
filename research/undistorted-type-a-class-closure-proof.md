---
rg: 2
id: undistorted-type-a-class-closure-proof
kind: route
title: Track word metrics through the Belk--Zaremsky quasi-retraction and Zaremsky's product and wreath constructions
target: undistorted-type-a-class-closure-and-qi-boone-higman
requires:
  - twisted-brin-thompson-groups-quasi-retract-onto-acting-group
  - twisted-brin-thompson-finite-presentation-criterion
  - boone-higman-type-a-class-closed-under-finite-extensions
  - hyperbolic-groups-undistortedly-embed-in-fp-simple-groups
  - hyperbolic-groups-lie-in-the-permutational-class
  - aut-free-groups-quasi-isometrically-embed-in-fp-simple-groups
  - braid-groups-quasi-isometrically-embed-in-fp-simple-groups
---

"Undistorted" means the inclusion of finitely generated groups is a quasi-isometric embedding. We use three
facts: compositions of undistorted inclusions are undistorted; finite-index inclusions are quasi-isometries;
automorphisms of finitely generated groups are bi-Lipschitz.

1. **QI Boone–Higman.** Let `G ≤ E` be undistorted, with `E` of type (A) on `S`.
   - `SV_E` is finitely presented (`twisted-brin-thompson-finite-presentation-criterion`) and simple.
   - `E` is undistorted in `SV_E` (`twisted-brin-thompson-groups-quasi-retract-onto-acting-group`). Compose.
2. **Subgroups and products.**
   - Undistorted subgroups: compose.
   - Products: if `G_i ≤ E_i` are undistorted, then `G_1 × G_2 ≤ E_1 × E_2` is undistorted for the product
     generating set. `E_1 × E_2` acts on `S_1 ⊔ S_2` with type (A) (Zaremsky Proposition 5.5, recorded in
     `boone-higman-type-a-class-closed-under-finite-extensions`).
3. **Finite-index overgroups.** Let `H ≤ G` have finite index, with `H ≤ E` undistorted.
   - Replace `H` by its normal core `H_0` in `G`. Then `H_0` has finite index in `H`, so it is still
     undistorted in `E`.
   - Kaloujnine–Krasner gives `κ: G → H_0 ≀ Q` with `Q = G/H_0` and `n = |Q|`. For `h ∈ H_0`,
     `κ(h) = (t_q^{-1} h t_q)_{q ∈ Q}`, where `t_q` is a fixed transversal. Each coordinate map is an
     automorphism of `H_0`, so `|κ(h)|_{H_0^Q} ≍ |h|`. Thus `κ` is a quasi-isometric embedding on `H_0`, and
     so on `G`.
   - `H_0 ≀ Q ≤ E ≀_n Σ_n` contains `H_0^n ≤ E^n` with finite index on both sides, so it is undistorted.
   - `E ≀_n Σ_n` acts on `S × {1,…,n}` with type (A) (Zaremsky Proposition 5.6, same node).
4. **Members.**
   - **Hyperbolic `G`.** `G` is undistorted in the full contracting RSG `Γ = [[G*Z | ∂_h(G*Z)]]`
     (`hyperbolic-groups-undistortedly-embed-in-fp-simple-groups`). `Γ` is a type (A) actor
     (`hyperbolic-groups-lie-in-the-permutational-class`).
   - **Aut(F_n).** `Aut(F_n)` is a retract of `Aut_V(V*F_n)`, which is a type (A) actor
     (`aut-free-groups-quasi-isometrically-embed-in-fp-simple-groups`). So is every group undistorted in it,
     for example `B_n`, `Mod(S_g^b)` with `b >= 1`, and `A(B_n)`
     (`braid-groups-quasi-isometrically-embed-in-fp-simple-groups`).
5. **Punctured spheres.** Put `P = PB_{m−1}`.
   - Its center is `⟨Δ²⟩`, and `Δ² = ∏_{i<j} A_{ij}`.
   - Let `χ: P → Z` be the coefficient of `A_{12}` in `P^{ab} = Z^{(m−1 choose 2)}`. Then `χ(Δ²) = 1`, so
     `P = ker χ × ⟨Δ²⟩` and `ker χ ≅ P/Z(P)`.
   - `P/Z(P) ≅ PMod(S_{0,m})` (Farb–Margalit, standard). So `PMod(S_{0,m})` is a retract of `P`, hence
     undistorted in `P`. `P` has finite index in `B_{m−1}`, so `PMod(S_{0,m}) ∈ QB_A`.
   - `Mod(S_{0,m})` is a finite-index overgroup of `PMod(S_{0,m})`, so step 3 applies.
6. **Genus two.**
   - Birman–Hilden: `Mod(S_2)/⟨ι⟩ ≅ Mod(S_{0,6})`, with `ι` the central hyperelliptic involution.
   - `Mod(S_2)` is residually finite (Grossman), so some finite-index `K ⊴ Mod(S_2)` avoids `ι`.
   - Then `K` maps isomorphically onto a finite-index subgroup of `Mod(S_{0,6})`, which lies in `QB_A` by
     steps 5 and 2.
   - Step 3 applies to `K ≤ Mod(S_2)`.
7. **Dihedral Artin groups.** `A(I_2(m))` is commensurable with `B_3` (BFFHZ, proof of Corollary B, citing
   Cumplido et al., Theorem 5). Apply steps 2 and 3. ∎
