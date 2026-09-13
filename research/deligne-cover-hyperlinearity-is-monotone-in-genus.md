---
rg: 2
id: deligne-cover-hyperlinearity-is-monotone-in-genus
kind: claim
title: Deligne's n-fold cover of Sp_2g(Z) embeds in that of Sp_2g+2(Z) preserving the covering generator, so every obstruction to approximating it propagates upward in genus
distinct_from:
  deligne-covers-of-sp2g-z-have-finite-residual-2z: that computes the finite residual of each cover at a fixed genus; this compares different genera through the block embedding.
  maslov-ce-parameter-set-is-a-closed-subgroup: that proves the Connes-embeddable twists of Sp_4(Z) form a closed subgroup; this proves that the Connes-embeddable twist sets can only shrink as the genus grows.
---

**ESTABLISHED** (`deligne-cover-hyperlinearity-is-monotone-in-genus-proof`). Unreviewed.

For `g >= 1` let `G_g = Sp_(2g)(R)`, with universal cover `p_g : G~_g -> G_g`, and let
`Gamma~_g = p_g^(-1)(Sp_(2g)(Z))`. `ker p_g = <z_g> ≅ Z`. For `1 <= n <= infinity` put
`E_n^(g) = Gamma~_g / <z_g^n>`, the preimage of `Sp_(2g)(Z)` in the connected `n`-fold cover. At
`g = 2`, `n = 3` this is the witness `E_3` of `deligne-central-mark-hs-collapse`. Let `iota` be the
block embedding `G_g -> G_(g+1)`, which fixes the last symplectic plane.

1. **Embedding.** `iota` lifts to an injective continuous homomorphism `iota~ : G~_g -> G~_(g+1)`
   with `iota~(z_g) = z_(g+1)` (after choosing generators compatibly) and
   `iota~(Gamma~_g) = p_(g+1)^(-1)(iota(Sp_(2g)(Z)))`. It induces injective homomorphisms
   `E_n^(g) -> E_n^(g+1)` sending the covering generator to the covering generator, for every `n`.
2. **Approximation properties descend in genus.** If `E_n^(g+1)` is hyperlinear, sofic, MF or
   linear sofic, so is `E_n^(g)`. Contrapositively, failure at genus `g` implies failure at every
   genus `g' >= g`.
3. **Mark collapse propagates upward.** Fix a metric class and an integer `k`. Suppose every
   asymptotic homomorphism of `E_n^(g)` sends `z_g^k` asymptotically to `1`, where asymptotic
   homomorphisms are pointwise. Then the same holds for `E_n^(g+1)` and `z_(g+1)^k`: restrict along
   item 1. This covers the normalized-HS statement `(DCM1)`, operator-norm emptiness of the
   nontrivial sectors, and the Frobenius collapse of
   `deligne-symplectic-covers-are-not-schatten-approximated`.
4. **Twist sets shrink.** Let `b_g` be an integral cocycle representing `Gamma~_g`, and let
   `E_CE^(g)` be the set of `t in R/Z` for which `L_(exp(2 pi i t b_g))(Sp_(2g)(Z))` is Connes
   embeddable. Then `E_CE^(g+1) <= E_CE^(g)`.
5. **The weakest triple-cover witness.** Let `E_3^(infinity) = union_g E_3^(g)` be the direct limit
   along item 1. The following are equivalent:
   - some `E_3^(g)` is not hyperlinear;
   - `E_3^(g)` is not hyperlinear for all large `g`;
   - `E_3^(infinity)` is not hyperlinear.

**Reading.** The graph poses the triple-cover problem at `g = 2`. That is the *strongest* instance,
since it implies every higher genus. Genus at least 3 is logically weaker and carries more
structure:
- `[T_2]` for `Gamma~_g` and Frobenius stability (`blsw-real-lattice-frobenius-stability`);
- the established unnormalized collapse.

Open target: `deligne-stable-triple-cover-is-not-hyperlinear`.

**Model test.** Upward propagation is consistent with the landed facts. The Frobenius collapse holds
at every `g >= 3` and is not asserted at `g = 2`, which is the direction item 3 forbids inferring. For
`n = 2` every `E_2^(g)` is residually finite, as the finite residual `<z_g^2>` shows, so there is no
obstruction to propagate.
