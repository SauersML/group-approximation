# sk-iso-rigidity part 2: diagonal recognition alone gives standardness (2026-09-13)

Lane sk-iso-rigidity. Part 1: `research/artifacts/sk-iso-rigidity-2026-09-13-part1.md` (Theorem P, Peirce
coordinatization). Everything here is UNREVIEWED and queued with sk-verify-13.

## 1. Theorem R

`diagonal-recognition-makes-subshift-el3-isos-standard` (route `-proof`).
- *Setting.* `X, Y` infinite minimal subshifts. `B ⊆ R_Y` is a maximal commutative subalgebra spanned by its
  idempotents.
- *Statement.* An isomorphism `α: G_X → G_Y` with `α(L_X)` conjugate in `G_Y` to `GL_3(B)` is standard: an inner
  automorphism composed with a ring isomorphism `M_3(R_X) ≅ M_3(R_Y)`, or with the graph-twisted form. So `X` and `Y`
  are strongly orbit equivalent.

**Proof in four moves.**
1. *Pointwise.* An isomorphism `LC(X,Q) → LC(Ω,Q)`, with `Q = GL_3(F_2)`, is `f ↦ β(f∘η^{-1})`, where `η` is a
   homeomorphism and `β: Ω → Aut(Q)` is locally constant. The points come from the reviewed Lemma B; the local
   automorphisms from supports of constant bumps.
2. *Normalize.* `Aut(Q) = Inn(Q) ⋊ ⟨inverse-transpose⟩`. Conjugating by a locally constant element of `GL_3(B) ⊆ G_Y`
   leaves `β` equal to the identity on a clopen set `Ω_1` and to the graph automorphism on `Ω_2 = Ω ∖ Ω_1`.
3. *Roots from their locally constant parts.* `C_G(A_12 ∩ L) = C_G(A_12)`, since a diagonal entry commuting with a
   maximal commutative idempotent-spanned subalgebra lies in it, and its units are trivial. With the reviewed
   bicommutant theorem, `A_ij = C(C(A_ij ∩ L))`, and the same holds for `{e_ij(b) : b ∈ B}` in `G_Y`. So `α(A_ij)` is
   the double centralizer of `{I + bpE_ij + bqE_ji}`, where `p = 1_{Ω_1}` and `q = 1_{Ω_2}`.
4. *No mixed orientation.*
   - If `q = 0`, `α` preserves root subgroups, and Theorem P applies with `E_k = E_kk`.
   - If `p = 0`, precompose with the graph automorphism of `G_X`.
   - If both are nonzero, `α(A_ij) = W_ijA_ij(R_Y)W_ij` with `W_ij = p + qP_(ij)`. A direct computation shows that
     `[W_12E_12W_12, W_23 sE_23 W_23]` has `(1,2)`-entry `psq`, while `M_13 = W_13A_13W_13` has zero `(1,2)`-entries.
     Simplicity of `R_Y` gives `s` with `psq ≠ 0`, which contradicts `[A_12,A_23] ⊆ A_13`.

## 2. What this changes

- Firewall F2 of `research/artifacts/sk-rigidity-intrinsic-reconstruction-2026-09-13-part1.md` split flip rigidity into:
  - (i) recognition: `α(L_X) = GL_3(A′)` for a Cartan-type `A′`;
  - (ii) Cartan uniqueness.
- Theorem R shows that (i) alone gives standardness and strong orbit equivalence, with no Cartan uniqueness. (ii) is
  only needed for the flip form.
- The whole SOE form of the note's question now reduces to one group-theoretic recognition statement:
  - **(Rec)** for every isomorphism `α: G_X → G_Y`, the image `α(L_X)` is `G_Y`-conjugate to `GL_3(B)` for a maximal
    commutative idempotent-spanned `B ⊆ R_Y`.
- **Sanity check against Petechuk's exceptional case.**
  - Over a product ring the "mixed orientation" maps are genuine non-standard automorphisms of `E_3`.
  - Step 4 kills them exactly because `R_Y` is simple, since `psq` vanishes when `p` is central.
  - This matches firewall F-PET: a proof must use simplicity.

## 3. Status of (Rec) and next attacks

- `α(L_X) ≅ LC(X, GL_3(F_2))` and `C_{G_Y}(α(L_X)) = 1` hold automatically.
- What must be shown: the `F_2`-span of `α(L_X)` is `M_3(B)` for a commutative `B` in standard position. Candidates:
  - *Finite subgroups.* Each finite subgroup `α(c_𝒫)` (constants on a clopen partition `𝒫`) is a
    `GL_3(F_2)^{|𝒫|}`-representation on `R_Y^3`.
    - The block idempotents of `F_2[GL_3(F_2)]` (principal and Steinberg blocks) give idempotents in `M_3(R_Y)`.
    - `C_{G_Y}(α(L_X)) = 1` and the product structure over `𝒫` might force the natural module, with multiplicity
      given by a projective `P` and `P³ ≅ R_Y³`.
  - *Characterize `L_X` intrinsically* (maximal locally finite? normalizer acting minimally on the maximal normal
    subgroups?), and show that every subgroup with these properties has the standard span.
- Obstacle: `F_2[GL_3(F_2)]` is not semisimple, so non-split extensions of the trivial module are possible a priori.

## 4. Credit

- Lemma B and the bicommutant theorem are reviewed nodes of sk-rigidity-intrinsic and sk-rigidity-f2.
- `Out(L_3(2)) = 2`, with the inverse-transpose as the outer automorphism, is recalled from Steinberg's description of
  automorphisms of Chevalley groups; no locator was checked.
- Novelty: a grep of main only.
