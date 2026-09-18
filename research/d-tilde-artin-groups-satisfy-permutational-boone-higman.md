---
rg: 2
id: d-tilde-artin-groups-satisfy-permutational-boone-higman
kind: claim
title: Every Euclidean Artin group of type D̃_n lies in B_A (open), with its reduction to a surface bundle over Conf_n(C) and the obstructions to the known fibre methods
distinct_from:
  artin-groups-satisfy-boone-higman: that is the open named problem over all Artin groups; this is the single Euclidean family D̃_n, which BFFHZ (after Corollary B) and survey Remark 5.4 list as open.
  b-tilde-artin-groups-via-one-cone-point-fibration: that settles B̃_n by fibring over the positions of the strands and the puncture; this records why the same move leaves a two-dimensional fibre for D̃_n, whose orbifold has two cone points.
  weyl-toric-arrangements-b-d-e-f-are-not-fiber-type: that rules out toric projections for D_n (n >= 4); this collects that and a second, symmetry obstruction.
artifacts:
  - research/artifacts/gq-bh-bh-verify-artin-euclidean-toric.md
---

**OPEN.** For every `n >= 4`, `A(D̃_n)` lies in `B_A`. So it embeds in a finitely
presented simple group, which is the survey's Problem 5.3(13) for this type. For
`n = 3`, `D̃_3 = Ã_3` is known.

## Reduction (lane proofs, not reviewed)

1. **Toric form.** By `euclidean-artin-toric-commensurability` with `L = Z^n`, the
   claim is equivalent to `π_1(N_D) ∈ B_A`, where
   `N_D = {v ∈ (C^×)^n : v_i ≠ v_j and v_i v_j ≠ 1 for i ≠ j}`.
2. **Homogenized form.** Let
   `E = {(c_1, c_2, x, y) : c_1 ≠ c_2, x ∈ Conf_n(C), y_k^2 = (x_k − c_1)(x_k − c_2)}`.
   Strands may sit at `c_1` or `c_2`, the two cone points. As in
   `b-tilde-artin-groups-via-one-cone-point-fibration-proof`, step 1 (with the
   condition `x_k ≠ c_1` dropped), `E ≅ Conf_2(C) × N_D`.
3. **Surface bundle.**
   - `(c, x, y) ↦ x` is a fibre bundle `E -> Conf_n(C)`. Its fibre `F_x` is the smooth
     connected `(Z/2)^n`-cover of `C^2 − {c_1 = c_2}` branched along the grid
     `{c_1 = x_k} ∪ {c_2 = x_k}`, with the `k`-th factor branched along both lines
     labelled `k`.
   - Local triviality: apply `φ × φ` for an isotopy `φ` of `C` moving `x`. It
     preserves the diagonal and the labelled grid.
   - Hence `1 -> π_1(F) -> Z × π_1(N_D) -> P_n -> 1`.
   - So the claim follows if `π_1(F)` is finitely generated free (it is not: `F` is a
     complex surface), or more generally if `π_1(F)` is centreless with
     `Aut(π_1 F) ∈ B_A`, or if the image of `Z × π_1(N_D)` in `Aut(π_1 F)` lies in
     `B_A` (`free-kernel-extensions-stay-in-the-permutational-class`, Lemma).
4. **Filling divisors.** `N_D = N_B ⊔ E_1 ⊔ … ⊔ E_n` with `E_k = {v_k = 1} ≅ N_B^(n−1)`.
   So `π_1(N_D) = π_1(N_B)/⟨⟨μ_1, …, μ_n⟩⟩`, where `μ_k` is a meridian of `E_k` and
   `π_1(N_B) ∈ B_A` (B̃_n). A homomorphic section of this quotient would settle the
   claim.

## Obstructions to the known methods

- **Toric projections.** The D_n toric arrangement is not fiber-type for `n >= 4`
  (`weyl-toric-arrangements-b-d-e-f-are-not-fiber-type`).
- **Invariant maps.** Let `σ_k: v_k ↦ v_k^(-1)`. No holomorphic `p: N_D -> B^(n−1)`
  with `p ∘ σ_k = p = p ∘ σ_(k')` (`k ≠ k'`) is a submersion at the points
  `v_k = 1, v_(k') = −1` (two strands on the two cone points). There `dσ_k` and
  `dσ_(k')` are `−1` on two independent directions, and `dp` must kill both
  (artifact, lemma).
  - Every map whose base coordinates depend on the strands through the orbifold
    positions `x_k` alone is of this kind. That includes the Li--Roushon construction
    and the one-cone-point bundle.
  - The same argument shows that no curve fibration of `F` factoring through
    `C^2 − Δ` has smooth fibres through the grid points `(x_k, x_(k'))`.
- **Retraction kernels.** The folding `s_0 ↦ s_1` is a retraction
  `A(D̃_n) -> A(D_n)`. Its kernel is not finitely generated free: otherwise
  `χ(A(D̃_n)) = (−1)^n` would equal `χ(K)·χ(A(D_n)) = 0`. Both Euler characteristics
  come from the Salvetti complex.

## Attempts

1. **Fibre over the strands and one cone point.** *Works exactly when strands avoid
   that cone point*, which is the B̃_n open subset (see above). Adding back strands at
   the second cone point creates multiple fibres over `{c_1 = x_k}`, and those
   branch points escape into the puncture. So `E -> Conf_n(C) × C` is not an orbifold
   bundle.
2. **Surviving shape.** A fibration, or an injective map into a free-by-`B_A` group,
   that uses the lifts `v_k` and not only their orbifold images. In orbifold terms:
   treat the two cone points asymmetrically.
3. **Every single-object fibre fails** (lane analysis, 2026-09-18). Consider fibrations whose fibre is the position of one object, with the others in the base: a cone point (as for B̃_n and B(e,e,n)), a strand, or the homogenized puncture (as in Li--Roushon's scaling).
   - A cone point as fibre coordinate: a strand on the *other* cone point makes a branch point fall into the puncture "cone points distinct".
   - A strand as fibre coordinate: another strand on a cone point merges its two lifted punctures `v_j, 1/v_j`.
   - The puncture as fibre coordinate: the count of punctures `±w_j` drops when a strand reaches a cone point.
   - Any of these could be repaired only by removing a divisor from the total space, which gives a quotient, not a subgroup.
   - More generally, a fibre through a point of `{strand k at c_1} ∩ {strand j at c_2}` must be smooth there, which forces it to be transverse to both divisors. By the invariance lemma the map must then genuinely use the lifts `v_k` (or `y_k`), not only orbifold positions.
4. **The filled space is a bundle, but only as a quotient.** In the double cover `E'` (coordinates `u_k^2 = x_k − c_1`, `z_k^2 = x_k − c_2`), allowing `c_1 = c_2` gives a genuine bundle `E'_fill -> C × M(D_n^lin)` with fibre a `(Z/2)^n`-cover of `C` branched at `n` points. So `π_1(E'_fill) ∈ B_A`. But `E' = E'_fill − {c_1 = c_2}`, so `π_1(E') -> π_1(E'_fill)` is only a surjection. Its kernel contains the normal closure of the twist of the two cone points about each other.
