---
rg: 2
id: pisot-unit-slope-stein-groups-are-finitely-presented
kind: claim
title: For every algebraic unit β > 1 with property (F), in every degree, the irrational-slope Stein group V(Z[β],⟨β⟩,ℓ) is finitely presented and its derived subgroup is a finite-index finitely presented simple group; a positive answer to Tanner's question for these slopes
requires:
  - pisot-stein-groups-are-contracting-rsgs
  - contracting-rsgs-embed-in-fp-simple-groups
distinct_from:
  stein-derived-groups-need-computable-modules: that is the necessary condition (computable module) for Tanner's question; this is a sufficient condition in every degree.
  norm-minus-one-sturmian-jm-groups-satisfy-boone-higman: that gets finite index of D(V) for quadratic metallic slopes and takes finite presentation from Cleary; this proves finite presentation directly, for all (F) units of any degree, with the same homology argument for finite index.
  pisot-stein-groups-are-contracting-rsgs: that proves the group is a contracting RSG and deduces the embedding into a finitely presented simple group; this adds that the Stein group is itself full, hence finitely presented by BBMZ Theorem A, and that its derived subgroup already is the finitely presented simple group.
artifacts:
  - research/artifacts/gq-bh-bh-near-actions-stein-slopes-reading.md
---

**ESTABLISHED** (lane proof, not reviewed; no priority claimed). Inputs:
- BBMZ Theorem A, "every full, contracting RSG is finitely presented" (`contracting-rsgs-embed-in-fp-simple-groups`,
  item 4);
- Tanner's simplicity theorem for `D(V)`;
- Li's groupoid homology and the AH exact sequence, as stated by Tanner (the same inputs (L), (S) as in
  `norm-minus-one-sturmian-jm-groups-satisfy-boone-higman`).

## Statement

Let `β > 1` be an algebraic unit with property (F), of degree `d ≥ 2`, and let `ℓ ∈ Z[β]`, `ℓ > 0`.

1. `V(Z[β],⟨β⟩,ℓ)` is finitely presented.
2. Its abelianization is finite, so `D(V(Z[β],⟨β⟩,ℓ))` has finite index. It is therefore finitely presented,
   and it is simple.

In degree 2 these are the metallic slopes, recovering Cleary's finite presentation. Beyond degree 2 this gives
finitely presented simple "irrational-slope Thompson groups" with slopes the tribonacci and d-bonacci
numbers, for example. **Tanner (arXiv:2312.07375) asks "Under what conditions is D(V(Γ,Λ,ℓ)) finitely
presented?"** This answers it positively for `Γ = Z[β]`, `Λ = ⟨β⟩`, with `β` any (F) unit.

## Proof

1. **Full.**
   - By `pisot-stein-groups-are-contracting-rsgs`, `V_β = V(Z[β],⟨β⟩,1)` acts on the β-shift `X_β` as a
     contracting RSG.
   - It is full. Take a homeomorphism of `X_β` that agrees locally with `V_β`. By compactness it agrees with
     elements of `V_β` on finitely many clopen pieces.
   - Clopen sets are finite unions of intervals with endpoints in `Fin(β) = Z[β] ∩ [0,1)`, by (F). So the
     homeomorphism is a right-continuous PL bijection with slopes in `⟨β⟩` and breakpoints in `Z[β]`, and lies
     in `V_β` by definition.
   - BBMZ Theorem A gives finite presentation.
   - **General `ℓ`.** Transport `V(Z[β],⟨β⟩,ℓ)` by `x ↦ β^{−m}x` onto the clopen set `E = π^{−1}[0,β^{−m}ℓ)`.
     There it is the full group of `V_β`-germs on `E`, again a full contracting RSG, now in `R_{Γ,E}`.
2. **Finite index.** Put `Γ = Z[β] ≅ Z^d`, with multiplication by `β` given by a matrix `A`.
   - **`H_0`.** `H_0 = Γ/(1−β)Γ` has order `|N(1−β)| ≠ 0`.
   - **`H_1 = H_2(Γ ⋊ Z)`.** It is an extension of `ker(1 − A) = 0` by `coker(1 − Λ²A)`. The eigenvalues of
     `Λ²A` are the products `β_iβ_j`, `i < j`, of distinct conjugates.
     - For a Pisot unit of degree `≥ 3`, none of these products is 1. Only `β` lies outside the unit disk, so
       `1/β` is not a conjugate.
     - In degree 2 the product is `N(β) = −1`, since (F) quadratic units satisfy `β² = mβ + 1`.
     - So `H_1` is finite.
   - **Conclusion.** The AH sequence `H_0 ⊗ Z/2 → V^ab → H_1 → 0` makes `V^ab` finite. So `D(V)` has finite
     index, and a finite-index subgroup of a finitely presented group is finitely presented. `D(V)` is simple by
     Tanner's theorem. ∎

## Remarks

- **Hosts.** These `D(V)` are finitely presented simple groups containing the interval exchange groups of
  `pisot-interval-exchange-groups-satisfy-boone-higman`, via derived subgroups. So they are explicit hosts
  there, without twisted Brin--Thompson groups.
- **`F_∞`.** Not claimed; BBMZ prove finite presentation only.
