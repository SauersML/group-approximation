---
rg: 2
id: separable-benign-witness-forces-rf-quotient-proof
kind: route
title: "Proof: inclusions are profinitely continuous, so closedness of Sigma passes to Sigma cap K; type FP_k subgroups of products of k limit groups are closed by a Goursat induction on top of Wilton and BHMS"
target: separable-benign-witness-forces-rf-quotient
requires:
  - two-occurrence-realizability-is-type-f-benignness
---

Verification tier: proposed-established. Items 1, 2, 3(b), 3(d), 4 and 5 are
elementary. Item 3(a) cites Wilton (limit groups are LERF), Burns--Romanovskii
(free products of LERF groups are LERF), Agol--Wise (closed hyperbolic
3-manifold groups are LERF) and Haglund--Wise (quasiconvex subgroups of
virtually compact special hyperbolic groups are virtual retracts). Item 3(c)
cites the full-subdirect finite-index theorem of Bridson--Howie--Miller--Short
(Ann. of Math. 170 (2009)): a full subdirect product of `n` nonabelian limit
groups that is of type `FP_n(Q)` has finite index. A referee should check these
citations; the arguments around them are complete.

The **profinite topology** on a group `G` has the cosets of finite-index
subgroups as a basis. A subgroup `H ≤ G` is closed iff it is an intersection of
finite-index subgroups. For `N ⊴ G`, `N` is closed iff `G/N` is residually finite.

## Step 1. Item 1

Let `ι : K -> Λ` be the inclusion. If `V ≤ Λ` has finite index, then
`ι^{-1}(V) = V ∩ K` has finite index in `K`. So `ι` is continuous for the
profinite topologies. Then `N = Σ ∩ K = ι^{-1}(Σ)` is closed in `K` if `Σ` is
closed in `Λ`. For `N ⊴ K`, closedness means `K/N` is residually finite. ∎

## Step 2. Item 2

`BS(2,3) = <a, b | b^-1 a^2 b = a^3>` is finitely presented and not residually
finite (Baumslag--Solitar). Subgroups of residually finite groups are residually
finite, and Higman's universal group `U` contains every finitely presented
group, so `U` is not residually finite either. Apply Step 1 with
`K = F`, `N = N_P`. ∎

## Step 3. Items 3(a), 3(b), 3(d)

- **(a)** In a LERF group, every finitely generated subgroup is closed by definition. Groups of type `F` are finitely generated.
- **(b)** Let `Λ_0 ≤ Λ` have finite index and let `r : Λ_0 -> Σ` be a retraction.
  - Then `Σ = {g ∈ Λ_0 : r(g) = g}`.
  - If `Λ` is residually finite, so is `Λ_0`, and its profinite topology is Hausdorff.
  - `r` is continuous: the preimage of a finite-index subgroup is of finite index. So the equalizer `Σ` of `r` and the identity is closed in `Λ_0`.
  - `Λ_0` is open and closed in `Λ`, and the topology of `Λ_0` is induced from `Λ` (a finite-index subgroup of `Λ_0` has finite index in `Λ`). So `Σ` is closed in `Λ`.
- **(d)** If `Σ ⊴ Λ` and `Λ/Σ` is residually finite, then `Σ` is closed.
  - Right-angled Artin groups are residually finite and `A_L/BB_L ≅ Z`.

In each case Step 1 applies. ∎

## Step 4. Item 3(c): tame subgroups

Call `H ≤ G` **tame** if `H` is closed in `G` and the topology induced on `H`
by the profinite topology of `G` is the full profinite topology of `H`.
(Equivalently: every finite-index subgroup of `H` contains `H ∩ W` for some
finite-index `W ≤ G`, and `H` is closed.)

- **(T1)** In a LERF group `L`, every finitely generated `H` is tame.
  - `H` is closed by definition. Let `H_0 ≤ H` have finite index, and let `H_1 ⊆ H_0` be its normal core in `H`.
  - `H_1` is finitely generated, hence closed in `L`, hence an intersection of finite-index subgroups of `L`.
  - For each of the finitely many coset representatives `h ∉ H_1` of `H/H_1`, pick a finite-index `W_h ⊇ H_1` with `h ∉ W_h`. Put `W = ∩_h W_h`.
  - `H ∩ W` is a union of `H_1`-cosets and misses every `h H_1 ≠ H_1`. So `H ∩ W = H_1 ⊆ H_0`.
- **(T2)** Finite-index subgroups are tame. If `H` is tame in `G` and `G` is tame in `G'`, then `H` is tame in `G'`. If `H_i` is tame in `G_i` for `i = 1, ..., k`, then `H_1 × ... × H_k` is tame in `G_1 × ... × G_k`: a finite-index `V ≤ ∏ H_i` contains `∏ (V ∩ H_i)`, and closed sets in the factors give closed products.
- **(T3) Goursat lemma.** Let `Σ ≤ X × Y` with `p_Y(Σ) = Y`. Put `Σ' = p_X(Σ)` and `C = Σ ∩ Y`. Assume `Σ'` is tame in `X` and `C` is tame in `Y`. Then `Σ` is tame in `X × Y`.

  *Proof.* `C` is normalized by `p_Y(Σ) = Y`. There is a homomorphism
  `f : Σ' -> Y/C` with `Σ = {(x, y) : x ∈ Σ', yC = f(x)}` (Goursat). `Y/C` is
  residually finite, since `C` is closed and normal.
  - *Closed.* Let `(x, y) ∉ Σ`.
    - If `x ∉ Σ'`, pick a finite-index `W ⊴ X` with `xW ∩ Σ' = ∅`. Then `(xW × Y) ∩ Σ = ∅`.
    - If `x ∈ Σ'`, write `f(x) = y_0 C`. Then `y_0^{-1} y ∉ C`. Pick a finite-index `V ⊴ Y` with `V ⊇ C` and `y_0^{-1} y ∉ V`.
    - `f^{-1}(V/C)` has finite index in `Σ'`. By tameness of `Σ'` there is a finite-index `W ⊴ X` with `W ∩ Σ' ⊆ f^{-1}(V/C)`.
    - If `(xw, yv) ∈ Σ` with `w ∈ W`, `v ∈ V`, then `w ∈ Σ' ∩ W` and `yvC = f(x) f(w) ∈ y_0 V/C`. So `y ∈ y_0 V`, a contradiction. So `(xW × yV) ∩ Σ = ∅`.
  - *Full.* Let `Σ_0 ≤ Σ` have finite index.
    - `C ∩ Σ_0` has finite index in `C`. By tameness of `C` there is a finite-index `V ⊴ Y` with `V ∩ C ⊆ Σ_0`.
    - `Σ_1 = Σ_0 ∩ (X × V)` has finite index in `Σ`, so `p_X(Σ_1)` has finite index in `Σ'`. Pick a finite-index `W ⊴ X` with `W ∩ Σ' ⊆ p_X(Σ_1)`.
    - Let `(w, v) ∈ Σ ∩ (W × V)`. There is `(w, v') ∈ Σ_1` with `v' ∈ V`. Then `(1, v v'^{-1}) ∈ Σ ∩ Y = C` and `v v'^{-1} ∈ V`. So it lies in `V ∩ C ⊆ Σ_0`, and `(w, v) = (1, v v'^{-1})(w, v') ∈ Σ_0`. ∎

**Theorem S(k).** If `L_1, ..., L_k` are limit groups and
`Σ ≤ L_1 × ... × L_k` is of type `FP_k(Q)`, then `Σ` is tame.

*Proof by induction on `k`.* For `k = 1`, `Σ` is finitely generated and
limit groups are LERF (Wilton), so (T1) applies. Let `k ≥ 2`.
- **Reduce to projections.** Put `H_i = p_i(Σ)`, finitely generated since `Σ` is. `H_i` is a limit group (finitely generated subgroups of limit groups are limit groups) and is tame in `L_i` by (T1). By (T2) it suffices to show that `Σ` is tame in `H = H_1 × ... × H_k`. Now `Σ` is subdirect in `H`.
- **Case A.** Every `H_i` is nonabelian and `Σ ∩ H_i ≠ 1` for every `i`. Then `Σ` is a full subdirect product of nonabelian limit groups of type `FP_k(Q)`. By BHMS it has finite index in `H`, so it is tame (T2).
- **Case B.** Otherwise there is an `i`, say `i = k`, with `H_k` abelian or `C = Σ ∩ H_k = 1`.
  - `C` is tame in `H_k`. If `C = 1`, this holds because limit groups are residually finite. If `H_k` is abelian, it is finitely generated free abelian, and every subgroup is tame.
  - `C` is finitely generated abelian, hence of type `FP_∞`. So `Σ' = p_{<k}(Σ) ≅ Σ/C` is of type `FP_k(Q)` (a quotient of an `FP_k` group by a normal `FP_∞` subgroup is `FP_k`, by the Lyndon--Hochschild--Serre argument), hence of type `FP_{k-1}(Q)`.
  - By S(k-1), `Σ'` is tame in `H_1 × ... × H_{k-1}`. By (T3) with `X = H_1 × ... × H_{k-1}` and `Y = H_k`, `Σ` is tame in `H`. ∎

Type `F` implies `FP_∞(Z)`, which implies `FP_k(Q)`. So every type `F` subgroup
of a product of `k` limit groups is closed, and Step 1 gives item 3(c).

## Step 5. Items 4 and 5

- **Item 4.** A finitely presented subgroup of `F_r × F_s` is of type `FP_2(Q)`, so it is closed by S(2), and Step 1 applies. The existence half is `mikhailova-fiber-product-gives-regular-mf-benign-compiler`.
- **Item 5.** Suppose `Λ` is finitely presented and `Σ` is finitely generated and closed.
  - Then membership in `Σ` is decidable (McKinsey's algorithm): enumerate the products of generators of `Σ`, and in parallel the finite quotients of `Λ`, looking for one that separates `g` from `Σ`.
  - Hence `Σ ∩ K` is recursive for every finitely generated `K ≤ Λ` given by words.
  - In the Boone tower, `Σ ∩ B = T_M` and `t(s) ∈ T_M` iff `s ∈ Hal`. So if `Hal` is not recursive, `Σ = <t, r_1, ..., r_n>` is not closed in `G'_M`. ∎
