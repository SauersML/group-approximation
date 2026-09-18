---
rg: 2
id: irrational-slope-v-tau-is-of-type-f-infinity-proof
kind: route
title: Golden subdivisions form an Ore category with the lcm-closed Garside family {id, L, R, M}; Witzel's criterion plus a bad-simplex argument over labelled matching complexes gives F_infinity for V_τ
target: irrational-slope-v-tau-is-of-type-f-infinity
requires:
  - irrational-slope-t-tau-and-v-tau-are-finitely-presented
---

**Inputs.**
- **Read at source.** Burillo–Nucinkis–Reeves (BNR), arXiv:2006.02401, `ttau.tex`: l.121 (two caret types)
  and Lemma `el-vt-lem` (l.134): every element of `V_τ` is a triple `(T_1, π, T_2)` of subdivision trees and
  a leaf permutation.
- **Read at source.** Witzel's criterion, *Classifying spaces from Ore categories with Garside families*,
  AGT 19 (2019), Thm. 3.12, as quoted in Li arXiv:2110.04505v2, Thm. `thm:Wit`. The hypotheses are:
  a cancellative, left reversible category with a Garside family `S` closed under factors; finite groups
  `C*(x,x)` (enough for `F_n`); a height function `ρ` with finite sublevel sets; and descending posets `E(x)`
  that are `(n−1)`-connected for `ρ(x) ≫ 0`. The conclusion is that `π_1(C,*)` is of type `F_n`.
- **Standard, not re-read.**
  - Björner–Lovász–Vrećica–Živaljević: `M(K_n)` is `(ν(n)−1)`-connected and weakly Cohen–Macaulay of
    dimension `ν(n) = ⌊(n−2)/3⌋`.
  - Hatcher–Wahl, Duke 2010, Prop. 3.5, on complete joins, as used in
    `abstract-twisted-bt-type-fn-colored-stein-proof`.
  - The bad-simplex argument (Hatcher–Wahl 2010 §2; Hatcher–Vogtmann, AGT 2017, Prop. 2.1).
- **On main.** (F) for the golden number `φ = 1/τ` (`pisot-stein-groups-are-contracting-rsgs`, metallic
  examples): `Fin(φ) = Z[τ] ∩ [0,1)`.

## 1. Admissible partitions

An *admissible partition* of an interval `I` is obtained from `{I}` by finitely many splits of a piece `J` by
either:
- `L`: `J` into its left part of length `τ|J|` and right part of length `τ²|J|`;
- `R`: `J` into left `τ²|J|` and right `τ|J|`.

Transport to `[0,1)` is by the increasing affine chart of `I`.

**Lemma A.** Let `P` be an admissible partition of `[0,1)`.
- (a) If `τ ∈ ∂P`, then `P = L·(P_1, P_2)` with `P_i` admissible on the two `L`-children.
- (b) If `τ² ∈ ∂P`, then `P = R·(P_1, P_2)` likewise.

*Proof.* Induction on the number of pieces. `P` is trivial or `P = s·(Q_1,Q_2)` with `s ∈ {L,R}` and `Q_i`
admissible with fewer pieces.
- **(a) with `s = R`.** The point `τ` lies in the child `[τ²,1)`, whose chart sends `τ` to
  `(τ−τ²)/τ = τ²`. By (b) for `Q_2`, `Q_2 = R·(Q_21, Q_22)`, so `P` has pieces `Q_1` on `[0,τ²)`, `Q_21` on
  `[τ²,τ)` and `Q_22` on `[τ,1)`. Since `τ² + τ³ = τ`, this is `L·(L·(Q_1,Q_21), Q_22)`.
- **(b) with `s = L`.** The point `τ²` lies in `[0,τ)` and charts to `τ`. By (a) for `Q_1`,
  `Q_1 = L·(Q_11,Q_12)`, and `P = R·(Q_11, R·(Q_12, Q_2))`.
- The other two cases are immediate. ∎

In particular `LL_1 = RR_2 =: M`, the split `(τ², τ³, τ²)`, where the subscript marks the child split
second.

**Lemma B (restriction).** If `P, P'` are admissible and `∂P ⊆ ∂P'`, then `P' = P·(P'|_J)_{J ∈ P}` with every
`P'|_J` admissible.

*Proof.* Induction on `P`. With `P = s·(P_1,P_2)`, the split point of `s` lies in `∂P'`, so Lemma A gives
`P' = s·(P'_1,P'_2)`. Recurse. ∎

**Lemma C (Ore).** Two admissible partitions of `[0,1)` have a common admissible refinement.

*Proof.* Let `Q_N` be the partition into golden β-cylinders of level `N`.
- It is admissible: it uses `L`-splits of state-A cylinders only.
- Its endpoints are the points of `Fin(φ)` of length `≤ N`.
- By (F), every breakpoint of either partition lies in `Fin(φ)`. Pick `N` above all their lengths and apply
  Lemma B. ∎

## 2. The category, the Garside family, the group

- **The category.** `C` has objects `n ≥ 1`. A morphism from `n` to `m` (merging `n` pieces into `m`) is
  `(P_1,…,P_m; σ)`: admissible partitions `P_i` of `[0,1)` with `Σ|P_i| = n`, and a bijection `σ` from
  `{1..n}` to the pieces. Composition is substitution (refinement). Units are the permutations, and
  `C*(n,n) = S_n` is finite.
- **Cancellative.** A composite determines the refinement of each piece (Lemma B), and, given the first
  factor, the grouping.
- **Left reversible.** This is Lemma C applied piecewise.
- **The Garside family.** Take `E = {id, L, R, M}` per piece, and let `S` be the elementary morphisms (each
  `P_i ∈ E`) together with the units.
  - **Closed under factors.** The only factorizations are `M = L·(L ⊔ id) = R·(id ⊔ R)` and the trivial ones.
    By Lemma B, the admissible coarsenings of `M` are `id, L, R, M`.
  - **Heads.** By Lemma A, the `E`-divisors of an admissible `P` are `id`, `L` (iff `τ ∈ ∂P`), `R` (iff
    `τ² ∈ ∂P`) and `M` (iff both, by Lemma B). This set has a maximum, so `S`-heads exist; merges read
    from the leaves are symmetric.
- **The group.** `π_1(C,1)` consists of fractions `(P, σ, P')`, and these are BNR's triples. By BNR Lemma
  `el-vt-lem` every element of `V_τ` is such a triple. Two triples defining the same map agree after a common
  refinement (Lemma C). So `π_1(C,1) ≅ V_τ`.
- **Height.** `ρ(n) = n`: non-invertible merges lower it, and each sublevel set is finite.

## 3. Descending links

`E(n)` is the poset of non-unit elementary merges from `n`, taken modulo target permutations and ordered by
`[α] ≤ [β]` iff `β = εα` with `ε ∈ S`. Its elements are *block systems*: disjoint blocks of pieces, each block
one of:
- a pair merged by `L(a,b)` (`a` left and long), `L(b,a)`, `R(a,b)` (`a` left and short) or `R(b,a)`;
- a triple `(a,b,c)` merged by `M`.

An `M`-block lies above exactly two pair-systems, `L(a,b)` and `R(b,c)`, and no other elementary morphism
refines to it (Lemma B). So `E(n)` is the face poset of the simplicial complex `K(n)`:
- its vertices are the labelled pairs;
- its simplices are the vertex sets of block systems, where an `M`-block contributes the *M-couple*
  `{L(a,b), R(b,c)}`.

Hence `|E(n)| ≅ K(n)`.

**Claim.** `K(n)` is `(ν(n)−1)`-connected.
- **The subcomplex.** Let `M_L(n) ⊆ K(n)` be the systems of pair blocks only: the labelled matching complex,
  a complete join over `M(K_n)` with 4-point fibres. It is `(ν(n)−1)`-connected (BLVZ plus Hatcher–Wahl
  3.5).
- **Bad simplices.** Call a simplex bad if it is a union of M-couples. A simplex with no bad face lies in
  `M_L(n)`, and a union of bad faces is bad.
- **Good links.** For a bad `σ` with `r ≥ 1` couples on `3r` pieces, the good link consists of the
  pair-systems on the other `n − 3r` pieces. A vertex meeting the support of `σ` could only complete a
  couple of `σ`, and those are complete. So the good link is `M_L(n−3r)`, which is
  `(ν(n) − r − 1)`-connected, since `ν(n−3r) = ν(n) − r`. This is at least `ν(n) − dim σ − 1 = ν(n) − 2r`.
- **Conclusion.** By the bad-simplex argument `(K(n), M_L(n))` is `ν(n)`-connected. With `M_L(n)`
  `(ν(n)−1)`-connected, `K(n)` is `(ν(n)−1)`-connected.

## 4. Conclusion

`ν(n) → ∞`, so for every `k` the posets `|E(n)|` are `(k−1)`-connected for `n ≫ 0`. Witzel's Theorem 3.12
gives `F_k` for all `k`. So `V_τ` is of type `F_∞`, and so is its finite-index subgroup `V_{xz}`. ∎

**Remark.** The only golden-specific inputs are Lemma A (the lcm `L ∨ R = M` is again elementary) and (F).
For other quadratic Pisot slopes with Winstone's tree pairs, there are `binom(a+b, a)` caret types. The analogue
of Lemma A, lcm closure in a finite elementary set, is what would need checking.
