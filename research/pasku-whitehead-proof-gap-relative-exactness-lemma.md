---
rg: 2
id: pasku-whitehead-proof-gap-relative-exactness-lemma
kind: claim
title: Pasku's claimed one-relator-deletion proof of Whitehead fails at its key relative exactness lemma, which alone already implies the theorem
distinct_from:
  contractible-2-complex-minus-a-cell-is-aspherical: that is the open type-(a) statement itself; this only shows that one claimed proof of it (arXiv:2107.12293v1) does not establish it, and locates the exact failing inference.
  kawauchi-weak-kervaire-rests-on-unresolved-inputs: that audits a different claimed chain (Kawauchi, four-dimensional inputs); this audits Pasku's Squier-complex argument at source level.
---

**ESTABLISHED** (source-level audit; full argument in the route `pasku-whitehead-proof-gap-relative-exactness-lemma-proof`).

**Object audited.** E. Pasku, *An answer to the Whitehead asphericity question*,
arXiv:2107.12293v1 (26 Jul 2021), unrefereed. The claimed theorem: if
`P = (x, r)` is an aspherical presentation of the trivial group and `r_0 ∈ r`,
then `P_1 = (x, r \ {r_0})` is aspherical. Via Ivanov's Theorem 1 the intro
says this would give the full Whitehead conjecture. Line numbers below refer
to the arXiv e-print `main.tex`.

**Statement.** Write `G_1` for the group of `P_1` and `D`, `D_1` for the Squier
complexes of the associated monoid presentations. Let `(D,p)` and `(D_1,p_1)`
be the paper's 3-complexes.

1. **The failing step.** The key Lemma `c-rel-ext` (l.1039–1062) proves that
   the sequence `0 → B_2(rel) → K_rel → B_1(D,D_1) → 0` is exact. In its proof
   (l.1051–1052), a 1-cycle of `D_1` lying in `J·s_1·ZF + ZF·s_1·J` is declared
   a boundary of square 2-cells of `D_1` by Kobayashi–Otto Theorem 6.6.
   - In the paper's own transcription of that theorem (l.393–402), `J` must be
     the ideal of the same presentation, here `J_1 = ker(ZF → ZG_1)`.
   - The paper uses `J = ker(ZF → ZG)` with `G = 1` instead.
   - The inference is false whenever `G_1 ≠ 1`. Explicit instance: take
     `P = ⟨x,y | x,y⟩`, `r_0 = y`, and `c = q(x,1)`. Then `(y − 1)·c` is a
     1-cycle of `D_1` in `J·s_1·ZF` but not in `B_1(D_1)`, because `y·c` and
     `c` lie in different components of `D_1`.
2. **The lemma is as strong as the theorem.** Assume `r_0 ≠ 1` in `G_1`. If the
   conclusion of Lemma `c-rel-ext` holds for `(P, r_0)`, then `P_1` is
   aspherical, by a five-line argument that uses none of the rest of the paper.
   - Take a square chain `σ = Σ ε_i [f, e_i]`, where `f` is an `r_0`-edge.
   - Its boundary is `−(ιf − τf)·c ∈ C_1(D_1)` for any 1-cycle `c` of `D_1`.
   - So `[σ]` lies in `ker ∂̂_2 ∩ K_rel`, and exactness forces `c ∈ B_1(D_1,p_1)`.
   - Hence `H_1(D_1,p_1) = 0`, which is asphericity of `P_1` by the paper's
     Theorem `asphh`.
3. **Where the step is valid, the theorem is trivial.** The inference is valid
   when `G_1 = 1`, because then `J_1 = J`. In that case (finite or
   countable), `K(P_1)` is a simply connected subcomplex of a contractible
   2-complex, so `H_2 = Z_2 ⊆ Z_2(K(P)) = 0` and `K(P_1)` is contractible.

**Consequence.** The crossed-module machinery (Props `quasi`, `free`, the
infinite-cyclic argument at l.1162–1185) cannot close the gap, since the gap
lemma by itself already implies the theorem. The type-(a) case, and the
Ivanov route to the full conjecture, stay open. The paper is not an input to
`whitehead-asphericity-conjecture` or `contractible-2-complex-minus-a-cell-is-aspherical`.
