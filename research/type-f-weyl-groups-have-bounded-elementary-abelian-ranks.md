---
rg: 2
id: type-f-weyl-groups-have-bounded-elementary-abelian-ranks
kind: claim
title: "Browder's exponent bound in a torsion-free Weyl pair: every elementary abelian p-subgroup of N(Sigma)/Sigma has rank at most 2 cd(Sigma) plus the p-ranks of Aut H_i(Sigma); so Higman's U (and V, and Z/2 wr Z) is not type F Weyl, and the normalized Weyl route to (d) is dead in type F"
distinct_from:
  u-weyl-pairs-need-out-sigma-to-contain-all-finite-simples: That pushes the finite subgroups of the Weyl group into Out(Sigma) and asks whether a type F Sigma can carry all large A_n there; this answers the Weyl-route question negatively without deciding that Out question, because the extension must be realized inside a torsion-free group, and Tate hypercohomology bounds its elementary abelian rank.
  normalized-benign-witnesses-give-the-semidirect-join: That proves U Weyl suffices for (d) and the root; this proves U is not type F Weyl, so that sufficient criterion is never met in type F.
  separable-benign-witness-forces-rf-quotient: That kills witnesses with profinitely closed Sigma, for any benign witness; this kills all F-normalized type F witnesses for N_U, separable or not, by a cohomological bound on the Weyl group.
---

**ESTABLISHED (proposed, 2026-09-18; referee welcome).**

**Theorem.** Let `Σ ⊴ E` with `E/Σ ≅ (Z/p)^r` for a prime `p`. Assume that
`E` is torsion-free, that `n = cd Σ < ∞`, and that every `H_i(Σ; Z)` is
finitely generated. Then

`r ≤ 2·#{1 ≤ i ≤ n : H_i(Σ; Z) ≠ 0} + Σ_{i=1}^{n} rk_p Aut H_i(Σ; Z) ≤ 2n + c_p(Σ)`,

where `rk_p` is the largest rank of an elementary abelian `p`-subgroup.
Each `rk_p Aut H` is finite for a finitely generated abelian `H`. So
`c_p(Σ)` depends only on `Σ` and `p`, and `c_p(Σ) = 0` whenever
`p > 1 + max_i dim H_i(Σ; Q)` and `p` divides no `|T_i|·|Aut T_i|`, where
`T_i = tors H_i(Σ; Z)`.

- **The trivial-action case.** If `E/Σ` acts trivially on `H_{≥1}(Σ; Z)`,
  then `p^r` divides `∏_{i=1}^{n} exp H^{i+1}(E/Σ; H_i(Σ; Z))`. This is
  Browder's exponent theorem (Invent. Math. 71, 1983), applied to the
  algebraic complex `Z ⊗_{ZΣ} P_*` of projective `Z[E/Σ]`-modules. The proof
  route gives a self-contained proof by Tate hypercohomology. Each factor
  divides `p^2`, and it divides `p` when `H_i` is torsion-free.

**Corollaries.**
1. **Weyl groups of torsion-free pairs.** Let `Σ ≤ Λ` with `Λ` torsion-free
   and `Σ` of finite cohomological dimension with finitely generated homology.
   For example, take any type `F` Weyl pair. Then every finite subgroup `Q` of
   `W = N_Λ(Σ)/Σ` has `rk_p Q ≤ 2 cd Σ + c_p(Σ)` for every prime `p`.
   - Apply the theorem to the preimage `E ≤ N_Λ(Σ)` of an elementary abelian
     `p`-subgroup of `Q`.
   - This includes every quotient `Γ/M` with `Γ` and `M ⊴ Γ` of type `F`.
2. **`U` is not type `F` Weyl.** Higman's universal group `U` contains
   `(Z/2)^r` for every `r`. So `U` embeds in no `W` as in item 1.
   Equivalently, `N_U ⊴ F(B)` has no `F(B)`-normalized type `F` witness.
   - The sufficient criterion "`U` is type `F` Weyl" of
     `normalized-benign-witnesses-give-the-semidirect-join` (item 4) never
     holds.
   - The Weyl route to (d), and through it to the root
     `every-re-normal-subgroup-of-a-free-group-is-type-f-benign`, is dead in
     type `F`.
   - The same holds for every torsion-free `F_m` variant whose `Σ` has finite
     cohomological dimension and finitely generated homology.
3. **Other groups excluded.** The following are not type `F` Weyl, since each
   contains `(Z/p)^r` for unbounded `r`:
   - Thompson's `V`;
   - `Z/2 ≀ Z`;
   - Grigorchuk's group;
   - `⊕_∞ Z/p`;
   - every group containing all finite groups.
   The type `F` Weyl class is contained in the class of groups whose finite
   subgroups have bounded `p`-rank for each `p`. It is still closed under free
   products (`weyl-class-closes-under-free-products-and-liftable-hnn`), and
   that closure is consistent with this bound.
4. **The `Out` question is bypassed.**
   `u-weyl-pairs-need-out-sigma-to-contain-all-finite-simples` asked whether a
   type `F` group `Σ` can have `A_n ≤ T(Σ)` for infinitely many `n`. The
   theorem does not decide that. `A_n ≤ Out(Σ)` could still be realized by
   extensions with torsion. What the theorem shows is that no torsion-free
   extension `Σ.A_n` exists once `2⌊n/4⌋ > 2 cd Σ + c_2(Σ)`, using
   `(Z/2)^{2⌊n/4⌋} ≤ A_n`.
   - This is the only kind of extension a Weyl pair of type `F` supplies.

**Calibration.**
- **Tori.** `Σ = Z^r ⊴ E = (p^{-1}Z)^r`, with trivial action and `r` nonzero
  `H_i`, all torsion-free. The refined bound (exponent `p` per torsion-free
  `H_i`) gives `r ≤ r`, which is sharp.
- **Finite quotients of free groups.** Take `F/N = (Z/p)^k` with
  `Σ = N ≅ F_R` and `R = 1 + p^k(rk F - 1)`. Then `n = 1`, and
  `c_p = rk_p GL_R(Z) ≥ ⌊R/(p-1)⌋ ≥ k`, so there is no contradiction. The
  bound is uniform only for a fixed `Σ`, which is exactly what a single Weyl
  pair gives.
- **Deep conjectures are not needed.** The sharper conjecture
  `Σ dim H_i(Σ; F_p) ≥ 2^r` is Carlsson's, and its algebraic form is false
  for odd `p` and `r ≥ 8` (Iyengar--Walker, 2018). The argument here uses
  only the linear exponent bound, which holds for every finite free, or
  projective, complex.

Proof: route `type-f-weyl-groups-have-bounded-elementary-abelian-ranks-proof`.

## Attempts

- **Beyond normalized witnesses, the rank invariant is replaced by rational
  cohomological dimension** (proposed-established, w11-117, 2026-09-18).
  - If `Σ ∩ F` is cut out by a compact open subgroup of a group acting with
    compact open stabilizers on a locally finite CAT(0) complex of dimension
    `d` (Bruhat–Tits buildings in any characteristic, products of trees,
    right-angled buildings, cube complexes), then `F/N` acts properly on the
    fixed set of `N`, so `cd_Q(F/N) ≤ d`.
  - `U`, `V` and Thompson's `F` contain `Z^n` for all `n`, so they have no
    such witness. Finite-subgroup ranks are genuinely unbounded from `d = 2`
    (`Z/2 ≀ Z` on `T_3 × T_3`, `SL_3(F_q[t])`), so the bound of this node has
    no geometric analogue there.
  - See `commensurated-cat0-witnesses-force-finite-rational-cd`.
