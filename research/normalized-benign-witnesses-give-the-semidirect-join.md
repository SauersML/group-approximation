---
rg: 2
id: normalized-benign-witnesses-give-the-semidirect-join
kind: claim
title: "The semidirect join is benign whenever the witness Sigma is normalized by H; so the F x F form of the benign root reduces to one fibre product F x_U F and follows from embedding U in a Weyl group N(Sigma)/Sigma of a type F pair, and it gives the full type F Higman benign theorem for r.e. subgroups"
distinct_from:
  type-f-normal-closure-lemma-is-the-whole-benign-problem: That proves root <=> normal-closure lemma and that (d), benignness of all finitely generated subgroups of F x F, implies the root, leaving the converse open as one semidirect join; this proves the semidirect join for normalized witnesses, reduces (d) to the single fibre product F x_U F, gives a sufficient Weyl-group criterion, and shows (d) implies type F benignness of every r.e. subgroup.
  every-re-normal-subgroup-of-a-free-group-is-type-f-benign: That is the open root (normal subgroups); this concerns the stronger statement (d) and the normalized form of witnesses that the root does not supply.
  separable-benign-witness-forces-rf-quotient: That kills separable witnesses as a class; this is a positive join construction that works for any witness, separable or not, as soon as H normalizes Sigma.
---

**ESTABLISHED (proposed, 2026-09-18; referee welcome).** Fix `m ∈ {2, ..., ∞}`
or `m = F`; `F_m`-benign and witnesses `(Λ, Σ)` are as in
`two-occurrence-realizability-is-type-f-benignness`. Call a witness `(Λ, Σ)`
for `L ≤ K` **`H`-normalized** if `H ≤ K` normalizes `Σ` inside `Λ`. For a
free group `F` and `N ⊴ F` put `P = F/N` and
`J_N = F ×_P F = {(u, v) : u v^{-1} ∈ N} = (N × 1)·ΔF ≤ F × F`.

1. **Semidirect join for normalized witnesses.** Let `L ≤ K` have an
   `F_m`-witness `(Λ, Σ)`, and let `H ≤ K` be of type `F_m`, normalizing `Σ`,
   with `H ∩ L = 1` (more generally with `H/(H ∩ L)` of type `F_m`). Then
   `(Λ, ΣH)` is an `F_m`-witness for `LH`: `ΣH ∩ K = LH`, and
   `ΣH ≅ Σ ⋊ H` is of type `F_m`.
2. **Normalized witnesses are Weyl-group embeddings.** Say `P` is
   **`F_m`-Weyl** if `P` embeds in `N_Λ(Σ)/Σ` for some groups `Σ ≤ Λ` of type
   `F_m`. For `N ⊴ F` the following are equivalent:
   - (i) `N` has an `F`-normalized `F_m`-witness;
   - (ii) `P = F/N` is `F_m`-Weyl.

   The class of `F_m`-Weyl groups contains every type `F_m` group (`Σ = 1`),
   every `Γ/M` with `Γ, M ⊴ Γ` of type `F_m` (`Σ = M`, torsion allowed), hence
   every finite group; it is closed under subgroups and finite direct products.
3. **(d) is one fibre product.** Statement (d) of
   `type-f-normal-closure-lemma-is-the-whole-benign-problem` (every finitely
   generated `S ≤ F × F` is `F_m`-benign) is equivalent to each of:
   - (d1) `J_N` is `F_m`-benign in `F × F` for every r.e. `N ⊴ F`;
   - (d2) `J_{N_U} = F(B) ×_U F(B)` is `F_m`-benign in `F(B) × F(B)`, for
     Higman's universal finitely presented group `U = F(B)/N_U`.

   Indeed every finitely generated `S ≤ P_1 × P_2` is a preimage
   `(λ × id)^{-1}(J_L)` (Goursat), and every `J_N` is a preimage of `J_{N_U}`.
4. **Sufficient criterion.** If `N ⊴ F` has an `F`-normalized `F_m`-witness
   then `J_N` is `F_m`-benign (item 1 with `L = 1 × N`, `H = ΔF`). Hence:
   if `U` is `F_m`-Weyl (equivalently, every finitely generated recursively
   presented group is `F_m`-Weyl), then (d) holds, and so does the root
   `every-re-normal-subgroup-of-a-free-group-is-type-f-benign`.
5. **(d) gives the full type F Higman benign theorem.** If (d) holds then
   every recursively enumerable subgroup `A` (normal or not) of every finitely
   generated free group `F` is `F_m`-benign. `A` is the equalizer of the two
   inclusions `F -> F *_A F`, i.e. the preimage of `J` of the double under
   `w -> (w, w̄)`.

So the implication root => (d) left open by the normal-closure claim is
**exactly** root => "`F ×_U F` is `F_m`-benign". A semidirect-join lemma for *arbitrary*
witnesses would give that implication; conversely that implication is the
only instance the converse needs (`L = 1 × N_U`, `H = ΔF`). Item 1 proves
the lemma for every witness in which `H` normalizes `Σ`.
What remains is the passage from an arbitrary witness for `N_U` to a
normalized one. This is not automatic: the Boone-tower witness
`Σ = <t, r_i> = <<t>>` for `T_M ≤ B` is not normalized by `B` whenever `T_M` is
not normal in `B`, since normalizing `Σ` would force `B` to normalize
`Σ ∩ B = T_M`.

Proof: route `normalized-benign-witnesses-give-the-semidirect-join-proof`.
