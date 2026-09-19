---
rg: 2
id: lacunary-hyperbolic-witness-kernels-are-non-rf-hyperbolic-proof
kind: route
title: The OOS stages of a lacunary hyperbolic group sandwich its relation module between two truncations of ratio C_2 k, so unbounded gaps or finite presentation follow, and the gap lemma finishes
target: lacunary-hyperbolic-witness-kernels-are-non-rf-hyperbolic
requires:
  - oos-lacunary-hyperbolic-short-relator-stages
  - relation-gaps-forbid-fp-mapping-tori
  - mapping-torus-mf-radical-lies-in-finite-residual
  - finitely-presented-lef-groups-are-residually-finite
  - fp-mapping-torus-iff-finite-automorphic-presentation
artifacts:
  - research/oos-lacunary-hyperbolic-short-relator-stages-citation.md
---

## 0. Conventions

- `F = F(S)` is free on the finite set `S`, and `K = F/N`.
- For `R ≥ 0`, `N_{≤R}` is the normal closure in `F` of `{w ∈ N : |w| ≤ R}`. These truncations
  increase with `R`, their union is `N`, and each is the normal closure of a finite set.
- A gap of ratio `C` at scale `R`, and property (UG), are as in
  `relation-gaps-forbid-fp-mapping-tori`.
- (S1)-(S4) refer to `oos-lacunary-hyperbolic-short-relator-stages`.

Two standard facts are used:
- (F1) Subgroups of sofic groups are sofic.
- (F2) A nontrivial torsion-free group is infinite. An infinite group with no nontrivial finite
  quotient is not residually finite, because every nonidentity element lies in every finite-index
  normal subgroup.

## 1. The sandwich lemma

**Lemma 1.** Let `K = F(S)/N` be lacunary hyperbolic, where the R-tree cone is taken with respect
to `S`. Let `d`, `H_n`, `C_2` and `n(k)` be as in (S1)-(S2). Write `H_n = F/M_n`, where `M_n` is
the normal closure of `R_n`, and put `ℓ_k = d_{n(k)} / (C_2 k)`. Then for every `k ≥ 1/C_2`:

```text
N_{≤ C_2 k ℓ_k} = N_{≤ d_{n(k)}} = M_{n(k)} = N_{≤ ℓ_k}.              (LHG)
```

*Proof.* Put `n = n(k)`.

**Upper bound: `M_n ⊆ N_{≤ ℓ_k}`.** By (S1), `K` is a quotient of `H_n`, through the canonical map
that is the identity on `S`, so `M_n ⊆ N`. By (S2), `M_n` is the normal closure in `F` of a
finite set `T_k` of words of length at most `ℓ_k`. Each `t ∈ T_k` lies in `M_n ⊆ N` and has
`|t| ≤ ℓ_k`, so `t` is one of the generators of `N_{≤ℓ_k}`. Hence `M_n ⊆ N_{≤ ℓ_k}`.

**Lower bound: `N_{≤ d_n} ⊆ M_n`.** Let `w ∈ N` with `|w| ≤ d_n`. Reading `w` from `1` traces a
closed path in `Γ(K, S)` of length at most `d_n`. Every vertex on it is within `d_n / 2 ≤ d_n` of
`1`, so the path lies in the ball of radius `d_n` about `1`.
- If "cycle" in (S1) means a closed path, then `w ∈ R_n ⊆ M_n` directly.
- If it means a simple cycle, prove by induction on length that the label of every closed path
  lying in the ball, based at any vertex, is in `M_n`. The empty word is trivially in `M_n`.
  - Suppose no vertex repeats except that the path ends where it starts. Then the path is either
    a simple cycle, so `w ∈ R_n`, or a backtrack `x x^{-1}`, which is freely trivial.
  - Otherwise the path visits the same vertex at positions `i < j` with `(i, j) ≠ (0, |w|)`.
    Write `w = a u b` as words, with `|a| = i` and `|au| = j`.
    - The subpath labelled `u` is a closed path of length `j - i`, with `1 ≤ j - i < |w|`.
    - The path labelled `ab` from the same base point is closed and uses only vertices of the original path. Its
      length is `|w| - (j - i)`, with `1 ≤ |w| - (j - i) < |w|`.
    - Both paths lie in the ball and both labels lie in `N`. By induction, `u` and `ab` lie in
      `M_n`, so `w = (a u a^{-1})(a b) ∈ M_n`.

    Here a cycle may be based anywhere in the ball: `R_n` contains the labels of all cycles in the
    ball, not only those through `1`.

Every generator of `N_{≤ d_n}` therefore lies in the normal subgroup `M_n`, so `N_{≤ d_n} ⊆ M_n`.

**Assembly.** `C_2 k ℓ_k = d_n`. For `k ≥ 1/C_2` we have `ℓ_k ≤ d_n`, so monotonicity of the
truncations gives

```text
N_{≤ ℓ_k} ⊆ N_{≤ d_n} ⊆ M_n ⊆ N_{≤ ℓ_k}.
```

All four groups are equal. ∎

**Lemma 2.** If `K` in Lemma 1 is not finitely presented, then `ℓ_k → ∞`, and `K` has (UG) over
`S`.

*Proof.* Suppose `ℓ_k ≤ B` for infinitely many `k`. For those `k`, (LHG) gives
`N_{≤ d_{n(k)}} = N_{≤ ℓ_k} ⊆ N_{≤ B}`. Now `n(k)` is strictly increasing and `d_n → ∞`, so
`d_{n(k)} → ∞`. Every `w ∈ N` therefore lies in some such `N_{≤ d_{n(k)}}`, which gives
`N = N_{≤ B}`. That is the normal closure of the finitely many relations of length at most `B`,
so `K` is finitely presented, a contradiction. Hence `ℓ_k → ∞`.

Now fix `C ≥ 1` and `R_0`. Choose `k ≥ max(1/C_2, C/C_2)` with `ℓ_k ≥ R_0`. Then

```text
N_{≤ ℓ_k} ⊆ N_{≤ C ℓ_k} ⊆ N_{≤ C_2 k ℓ_k} = N_{≤ ℓ_k}.
```

Moreover `N_{≤ ℓ_k} ≠ N`, because `K` is not finitely presented. This is a gap of ratio `C` at
the scale `ℓ_k ≥ R_0`. ∎

**Theorem part 1.** Suppose first that `K` is finitely presented. Then by (S3) `K` is hyperbolic.
Also `N = N_{≤ B}` for some `B`, so the truncations in (LHG) equal `N` as soon as `ℓ_k ≥ B`.
Otherwise Lemma 2 gives (UG), and `N_{≤ ℓ_k} ≠ N` for every `k`. A hyperbolic group is finitely
presented, so the two cases are exclusive. ∎

## 2. Tori and split extensions (Theorem part 2)

Let `K` be lacunary hyperbolic. By definition `K` is finitely generated. Let `H` be finitely
presented and `φ: H → Aut(K)` any action, and suppose `K ⋊_φ H` is finitely presented. Choose `S`
as in Lemma 1.

Suppose `K` were not finitely presented. Then Lemma 2 gives (UG) over the finite generating set
`S`. Part B of `relation-gaps-forbid-fp-mapping-tori` (Part A when `H = Z`) then says `K ⋊_φ H` is
not finitely presented, a contradiction. So `K` is finitely presented, and by (S3) it is
hyperbolic. ∎

## 3. Flagship witnesses (Theorem part 3)

Let `(G, K)` satisfy (TFZ1), and suppose `K` is quasi-isometric to a lacunary hyperbolic group.

1. `K` has property (T), so it is finitely generated. By (S4), `K` is lacunary hyperbolic for some
   finite generating set `S`.
2. `G/K ≅ Z` is free, so the extension splits: `G = K ⋊_ψ Z` for some `ψ ∈ Aut(K)`. `G` is
   finitely presented, so by part 2 `K` is a finitely presented hyperbolic group.
3. `K` is nontrivial and has property (T) by (TFZ1). It is torsion-free because `G` is, and it is
   sofic by (F1).
4. `Rad_MF(G) = K = K × {0}`, and `K` is finitely generated. So (FRB2) of
   `mapping-torus-mf-radical-lies-in-finite-residual` gives `R_fin(K) = K`: `K` has no nontrivial
   finite quotient.
5. By (F2), `K` is not residually finite.

So `K` is a torsion-free word-hyperbolic group that is not residually finite. It is also a
finitely presented sofic group with property (T) that is not residually finite. Since `K` is
finitely presented, the witness lies in region (AT) of
`finite-outer-order-radical-witnesses-cross-alekseev-thom`, not in (IO). ∎

## 4. The automorphic branch (Theorem part 4)

Let `(K, φ)` satisfy (P1) and (P2), with `K` lacunary hyperbolic.

1. (P1) makes `K` Kazhdan, hence finitely generated. By
   `fp-mapping-torus-iff-finite-automorphic-presentation`, (P2) is equivalent to finite
   presentation of `K ⋊_φ Z`.
2. By part 2, `K` is a finitely presented hyperbolic group. It is torsion-free and Kazhdan by
   (P1).
3. A nontrivial finite quotient `F` of `K` would be an MF quotient, and the MF radical dies in
   every MF quotient. So `Rad_MF(K) = K` forces `F = 1`. This is the "forced features" item of the
   target node.
4. Hence, by (F2), `K` is not residually finite.

The target node's design needs an infinitely presented `K`. Every lacunary hyperbolic `K` is
instead finitely presented. ∎

## 5. The LEF branch (Theorem part 5)

Let `(K, φ)` satisfy (LK1)-(LK3), and suppose `K` is quasi-isometric to a lacunary hyperbolic
group.

1. `K` is Kazhdan, hence finitely generated, and by (S4) it is lacunary hyperbolic.
2. By (LK2) and part 2, `K` is finitely presented.
3. `K` is LEF by (LK1). By `finitely-presented-lef-groups-are-residually-finite`, `K` is residually
   finite. Since `K` is nontrivial, it has a nontrivial finite quotient.
4. But (LK3) and (FRB2) give `R_fin(K) = K`: no nontrivial finite quotient. Contradiction. ∎

## 6. Conditional kill (Theorem part 6)

Under either hypothesis, parts 3 and 4 produce a contradiction:
- If every hyperbolic group is residually finite, it contradicts the non-residually-finite
  hyperbolic group `K`.
- If every finitely presented sofic Kazhdan group is residually finite, it contradicts `K` being
  finitely presented, sofic and Kazhdan without finite quotients. In part 4, `K` is sofic by (P1).
∎

## 7. What dies, and the invariant

**Class killed.** Every (IO) witness of `torsion-free-sofic-exact-mf-radical-over-z` whose kernel
is quasi-isometric to a lacunary hyperbolic group. That is every kernel with one R-tree
asymptotic cone, equivalently (OOS Theorem 3.3) every direct limit of hyperbolic groups with
`δ_i = o(r_{S_i}(α_i))`. Unconditionally, all such kernels are excluded from (IO), from the
intended infinitely presented branch of the automorphic node, and from (LK1)-(LK3).

- **Invariant.** The relation-gap ratio. On OOS stages it is at least `d_{n(k)} / ℓ_k = C_2 k → ∞`.
  This is the metric shadow of `δ_i / r_i → 0`: the hyperbolicity constant bounds the relator
  lengths of a stage, and the injectivity radius bounds from below the length of every new
  relation.
- **Death step.** Finite presentation of the torus: (FAP1), (L3), (LK2), or the finite
  presentation of `G` in (TFZ1). At a gap scale of ratio `L_ψ` the truncation is `ψ`-invariant.

**Members, beyond w15 Part C.**
- Every lacunary hyperbolic group with no graded small cancellation presentation.
- Every group quasi-isometric to a lacunary hyperbolic group, for example finite-index subgroups
  and finite extensions of Tarski monsters.
- Every sparse limit of hyperbolic stages in the style of
  `sofic-hyperbolic-stages-give-quotientless-kazhdan-monster`, and every Hull--Osin style limit
  `R / ∪ N_k` of a hyperbolic `R` whose stage constants are little-o of the stage injectivity
  radii.

In none of these cases is any hypothesis on MF, soficity, (T) or the automorphism used.

**What survives.** An (IO) kernel has no asymptotic cone that is an R-tree. If it is a direct
limit of hyperbolic groups at all, as with Burnside-type limits, the ratio `δ_i / r_i` stays
bounded below along every presentation as a limit.
