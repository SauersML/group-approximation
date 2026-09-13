---
rg: 2
id: simple-kazhdan-lef-group-from-minimal-subshift-proof
kind: route
title: Kazhdan by Ershov--Jaikin-Zapirain, simple by tower root detection, LEF by periodic return-word models
target: simple-kazhdan-lef-group-from-minimal-subshift
requires: [subshift-elementary-group-is-simple-modulo-centre, minimal-subshift-algebra-is-simple-lef-ring, elementary-groups-over-fg-rings-have-property-t]
artifacts:
  - research/artifacts/simple-kazhdan-lef-subshift-elementary-group-2026-09-12.md
  - research/artifacts/ex-review-groups-2026-09-12-part1.md
---

Put `R = LC(X,F_q) ⋊ Z`, `G = EL_3(R)` and `S = G/Z(G)`.

1. **Infinite and simple.** By `subshift-elementary-group-is-simple-modulo-centre`, every normal
   subgroup of `G` is central or all of `G`, and `Z(G) ⊆ F_q^x I_3` is finite. So `S` is simple.
   `e_12(LC(X,F_q)) <= G` is infinite, so `S` is infinite.
2. **Kazhdan.** `R` is a finitely generated ring with 1 (`minimal-subshift-algebra-is-simple-lef-ring`,
   item 1). `G` has property (T) by `elementary-groups-over-fg-rings-have-property-t`, and so does
   its quotient `S`.
3. **LEF.** Item 3 of `minimal-subshift-algebra-is-simple-lef-ring` gives an injective unital
   `Psi : R -> prod_omega M_(N_k)(F_q)`, hence `G <= prod_omega GL_(3N_k)(F_q)`. Put
   `Λ = {λ : λ I_3 ∈ G}`, so `Z(G) = Λ I_3`. `Psi` is `F_q`-linear, so `Psi(λ I_3) = λ I`, and
   `Psi(g) ∈ [Λ I]` forces `g ∈ Z(G)`. So `S` embeds in `prod_omega (GL_(3N_k)(F_q)/Λ I)`, an
   algebraic ultraproduct of finite groups. A finitely generated subgroup of such an ultraproduct is
   LEF.
4. **Sofic and hyperlinear.** Left regular permutation models of the finite approximants give sofic
   models, and permutation matrices give hyperlinear models.

**Review.** Independent re-derivation by lane `ex-verify-groups`, commit 0efeac410. Every item
passed: periodic models, the quotient by the centre, root detection cases (c) and (d), the
Ershov--Jaikin-Zapirain hypotheses, and the statement of Pestov 9.1 against the PDF. Its two wording
notes are applied: for `q` not prime, `F_q`-scalars are added to the ring generators and to `Σ_L`.
