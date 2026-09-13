# Homology of derived full groups and finite presentation, part 1: the Li filtration of `H_2`

Lane `ex-fp-simple-full-group-obstruct`, 2026-09-13. **Unreviewed.** Every statement below is
derived here from the cited theorems; the derivations are complete, and the imports are named.
Part 2 (`full-group-homology-fp-obstruction-labbe-2026-09-13.md`) treats Labbé's shift.

## 0. Outcome

- **Theorem 1.** For a minimal ample groupoid `G` with comparison and no isolated units,
  `H_2(D(G); Z) ≅ π_2 K(B_G)`. This group carries a three-step filtration whose graded pieces
  are subquotients of `H_2(G; Z)`, `H_1(G; Z/2)` and `H_0(G; Z/2)`.
- **Corollary 2 (obstruction for a class).** If `H_0(G; Z/2)` or `H_1(G; Z/2)` is infinite
  (while `H_2(G; Z/2)` is finite and `H_3(G; Z)` finitely generated), then `D(G)` is not
  finitely presented. If all `H_p(G; Z)`, `p <= k`, are finitely generated, then all
  `H_j(D(G); Z)`, `j <= k`, are finitely generated.
- **Theorem 3 (free minimal `Z^2`-systems).** `H_2(D([[Z^2 ~ X]]); Z)` is finitely generated
  iff `H^1(Z^2; C(X, Z/2))` and `H^2(Z^2; C(X, Z/2))` are finite. In that case it is
  `Z ⊕ T` with `T` a finite abelian 2-group of exponent at most 4.
- **Theorem 4 (Penrose).** `H_2(D(𝒫); Z) ≅ Z ⊕ T` with `|T| ∈ {2^12, 2^13}` and exponent at
  most 4. Every `H_j(D(𝒫); Z)` is finitely generated. So homology with trivial coefficients
  cannot refute finite presentation of `D(𝒫)`.
- **Proposition 5.** Every conjugation-invariant additive invariant of relations, for instance
  the mean signed area of relator loops against the invariant measure, factors through
  `N/[F,N]`. That group is finitely generated whenever `H_2` is. So the invariant-measure
  "relation compression" invariants of additive type are subsumed by Theorem 4, and they die with it.

## 1. Source: Xin Li, arXiv:2209.08087

We read the TeX source `main.tex`, whose e-print name is `Homology_TFG.tex` (modified 2024-11-25), on MSI at
`/scratch.global/sauer354/ex/ex-fp-simple-full-group-obstruct/src/2209.08087/`. Line numbers
refer to that file.

- **(L1)** Theorem `thm:HKB=HG`, lines 2086–2088: "Let `G` be an ample groupoid with locally
  compact Hausdorff unit space `G^(0)` and `C` an abelian group. We have
  `H~_*(K(B_G), C) ≅ H_*(G, C)`."
- **(L2)** Corollary `cor:HDG=HtiOKB`, lines 2681–2686: "Let `G` be an ample groupoid, with
  locally compact Hausdorff unit space `G^(0)` without isolated points. Assume that `G` is
  minimal and has comparison. Then `H_*(D(G), C) ≅ H_*(D(R × G), C) ≅ H_*(Ω~^∞_0 K(B_G), C)`
  for all abelian groups `C` and all `* >= 0`."
  - Line 2652 defines `Ω~^∞_0 K(B_G)` as the universal cover of `Ω^∞_0 K(B_G)`.
  - Line 2650 defines `D(G)` as the commutator subgroup of the topological full group `F(G)`.
- **(L3)** The proof of Theorem `thm:H2H0H1H1`, line 3066: "The Atiyah-Hirzebruch spectral
  sequence ... has `E^2_{p,q} = H~_p(K(B_G), π_q(S))` and converges to `π_{p+q}(K(B_G))`". It is a
  first-quadrant spectral sequence.
- **(L4)** Line 996: for a transformation groupoid, `H_*(Γ ⋉ X, C) ≅ H_*(Γ, C_c(X, C))`.
- **(L5)** Line 825: a free action of a countably infinite `Γ` on a compact metrizable totally
  disconnected `X` has comparison if the finitely generated subgroups of `Γ` have
  subexponential growth [Downarowicz–Zhang].
  - Line 839: tiling groupoids of aperiodic repetitive FLC tilings are étale and minimal, with
    Cantor unit space, and almost finite [IWZ], hence have comparison.
- **(L6)** Lines 3282–3292: "let `G` be the groupoid attached to the classical Penrose tiling.
  Then `H_*(G) ≅ Z^8` for `*=0`, `Z^5` for `*=1`, `Z` for `*=2`, `{0}` otherwise."
- **(L7)** Line 3043: groupoid homology is Morita invariant [Mat12, §3], [Mil, §4].
- **(L8)** Line 1162: `A(G) = D(G)` for almost finite or purely infinite minimal effective
  Hausdorff groupoids with Cantor unit space.

**Scope of the source check.** The only mention of finiteness properties in the source is
line 1199, background on type `F_n`. Li draws no finite-presentation consequence. Web search
was unavailable, so novelty of Corollary 2 and Theorem 3 is **not claimed**.

**Universal coefficients.** Groupoid homology is the homology of the complex `C_c(G^(n), Z)`.
- Each term is free abelian. It is an increasing union, along split injections, of the free
  groups `Z^P` for finer and finer clopen partitions `P`.
- Hence `H_n(G; A) ≅ H_n(G) ⊗ A ⊕ Tor(H_{n-1}(G), A)`.

## 2. Theorem 1: the filtration of `H_2(D(G))`

**Setting.**
- `G` is ample, and its unit space is locally compact Hausdorff without isolated points.
- `G` is minimal and has comparison.
- `K = K(B_G)` is Li's connective algebraic K-theory spectrum.

**Statement.**
- `H_2(D(G); Z) ≅ π_2(K)`.
- `π_2(K)` has a filtration `0 ⊆ F_0 ⊆ F_1 ⊆ F_2 = π_2(K)` with:
  - `F_0 ≅ H_0(G; Z/2) / ( d^2 H_2(G; Z/2) + d^3 E^3_{3,0} )`, where `E^3_{3,0} ⊆ H_3(G; Z)`;
  - `F_1 / F_0 ≅ H_1(G; Z/2) / d^2 H_3(G; Z)`;
  - `F_2 / F_1 ≅ ker( d^2 : H_2(G; Z) -> H_0(G; Z/2) )`.

*Proof.*
1. **Homology equals homotopy.** By (L2) with `C = Z`, `H_2(D(G)) ≅ H_2(Y)`, where
   `Y = Ω~^∞_0 K` is simply connected.
   - Hurewicz gives `H_2(Y) ≅ π_2(Y)`.
   - A covering map is an isomorphism on `π_k` for `k >= 2`, and `π_k(Ω^∞_0 K) = π_k(K)` for
     `k >= 1`.
   - So `H_2(D(G)) ≅ π_2(K)`.
2. **The `E^2` page.** By (L1) with `C = π_q(S)`, the spectral sequence (L3) has
   `E^2_{p,q} ≅ H_p(G; π_q(S))`. The stable stems are `π_0(S) = Z` and
   `π_1(S) = π_2(S) = Z/2`.
3. **Differentials in total degree 2.** They are `d^r : E^r_{p,q} -> E^r_{p-r, q+r-1}`.
   - `(0,2)`: `d^2` arrives from `(2,1) = H_2(G; Z/2)`, and `d^3` from `(3,0) ⊆ H_3(G)`.
     For `r >= 4` the source `(r, 3-r)` has `q < 0`. Outgoing differentials land at `p < 0`.
   - `(1,1)`: `d^2` arrives from `(3,0) = H_3(G)`, and `d^3` from `(4,-1) = 0`. Outgoing
     `d^2` lands at `(-1, 2)`.
   - `(2,0)`: outgoing `d^2` lands in `(0,1) = H_0(G; Z/2)`, and outgoing `d^3` at `(-1,2)`.
     Incoming differentials come from `q < 0`.
4. **Convergence.** First-quadrant convergence gives `F_p / F_{p-1} = E^∞_{p, 2-p}`. ∎

**Model tests.**
- **Thompson's `V`.** For `G_2`, all `H_*(G_2)` vanish (line 760), so `π_2 K = 0`, matching
  `H_2(V) = 0`.
- **Cantor minimal `Z`-systems.** Here `H_0(G) = K^0(X)` is torsion-free, `H_1(G) = Z`, and
  `H_k(G) = 0` for `k >= 2`. So `H_2(G; Z/2) = 0` and `H_1(G; Z/2) = Z/2`.
  - `H_2(D(G))` is therefore an extension of `Z/2` by `K^0(X) ⊗ Z/2`.
  - For a Sturmian system it has order 8. Matui's theorem (math/0404117) says such `D(G)` is
    never finitely presented, and homology does not see that.
  - For a minimal subshift with `K^0 ⊗ Z/2` infinite, Theorem 1 gives a second proof.

## 3. Corollary 2: an obstruction for a class, and a finiteness criterion

**Corollary 2.** Assume the setting of Theorem 1.
- **(a) Obstruction.** Suppose `H_3(G; Z)` is finitely generated and `H_2(G; Z/2)` is finite. If
  `H_0(G; Z/2)` or `H_1(G; Z/2)` is infinite, then `H_2(D(G); Z)` is not finitely generated,
  so `D(G)` is not finitely presented.
- **(b) Degree 2.** If `H_2(G; Z)`, `H_1(G; Z/2)` and `H_0(G; Z/2)` are finitely generated, then
  `H_2(D(G); Z)` is finitely generated.
- **(c) All degrees.** If `H_p(G; Z)` is finitely generated for every `p <= k`, then
  `H_j(D(G); Z)` is finitely generated for every `j <= k`.

*Proof.*
- **(a)** A finitely presented group has a `K(π,1)` with finite 2-skeleton, so its `H_2` is
  finitely generated.
  - In the filtration, `F_0` is `H_0(G; Z/2)` modulo the image of a finite group and of a
    finitely generated group. An infinite `F_2`-vector space stays infinite modulo a finitely
    generated subgroup. The same holds for `F_1/F_0`.
  - A finitely generated abelian group has finitely generated subquotients.
- **(b)** Every graded piece is finitely generated.
- **(c)** By universal coefficients, every `E^2_{p,q}` with `p + q <= k` is finitely generated,
  since `π_q(S)` is finitely generated. So `π_j(K) = π_j(Y)` is finitely generated for
  `2 <= j <= k`.
  - `Y` is simply connected. Serre's mod-`C` Hurewicz theorem, for the class `C` of finitely
    generated abelian groups, gives `H_j(Y)` finitely generated for `j <= k`. ∎

## 4. Theorem 3: free minimal `Z^2` Cantor systems

**Setting.** `Z^2` acts freely and minimally on the Cantor set `X`, and `G = Z^2 ⋉ X`.

**Preliminaries.**
- **(a) Hypotheses.** `G` meets the hypotheses of Theorem 1: comparison holds by (L5), and `X`
  has no isolated points. By (L8), `D(G) = A(G)`, the group of the neighbouring nodes.
- **(b) Duality.** `H_k(G; A) ≅ H_k(Z^2; C(X, A))` by (L4).
  - The Koszul resolution `0 -> Z[Z^2] -> Z[Z^2]^2 -> Z[Z^2] -> Z` is self-dual. Hence
    `H_k(Z^2; M) ≅ H^{2-k}(Z^2; M)` for every module `M`.
  - So `H_3(G; A) = 0`.
  - `H_2(G; A) ≅ H^0(Z^2; C(X, A))`, the invariant continuous functions. By minimality these
    are constant, so `H_2(G; A) = A`.
- **(c) Filtration.** Theorem 1 gives:
  - `F_0 ≅ H^2(Z^2; C(X, Z/2))` modulo the image of `Z/2`;
  - `F_1/F_0 ≅ H^1(Z^2; C(X, Z/2))`;
  - `F_2/F_1 ≅ ker( Z -> H_0(G; Z/2) )`, which is `Z` or `2Z`, and in either case `≅ Z`.

**Theorem 3.**
- `H_2(D([[Z^2 ~ X]]); Z)` is finitely generated iff `H^1(Z^2; C(X, Z/2))` and
  `H^2(Z^2; C(X, Z/2))` are both finite.
- In that case `H_2(D) ≅ Z ⊕ T`. Here `T = F_1` is a finite abelian 2-group of exponent at most 4,
  and `|T| = |F_0| · |H^1(Z^2; C(X, Z/2))|` with `|H^2|/2 <= |F_0| <= |H^2|`.

*Proof.*
- **Criterion.** The criterion follows from (c) and Corollary 2(a),(b).
- **Structure of `T`.** `F_1` is an extension of one `F_2`-vector space by another, so
  `4 F_1 = 0`. Since `F_2/F_1 ≅ Z` is free, `π_2 = F_1 ⊕ Z`. ∎

**Remarks.**
- For subshifts, `H^j(Z^2; C(X, A))` is the pattern-equivariant, equivalently Čech, cohomology of
  the tiling space. Li line 1002 records `H_*(G) ≅ Ȟ^{2-*}(Ω)`.
- **Consequence (class obstruction).** `D([[Z^2 ~ X]])` is not finitely presented whenever
  `H^1(Z^2; C(X, Z/2))` or `H^2(Z^2; C(X, Z/2))` is infinite.
- **Products.** Let `X = X_1 × X_2`, a product of Cantor minimal `Z`-systems with the product
  action. The action is free and minimal, and it is a `Z^2`-subshift when both `X_i` are subshifts.
  - Over the field `F_2`, `C(X, F_2) = C(X_1, F_2) ⊗ C(X_2, F_2)`. Künneth for `Z × Z` gives
    `H^2 ≅ (K^0(X_1) ⊗ Z/2) ⊗ (K^0(X_2) ⊗ Z/2)` and
    `H^1 ≅ (K^0(X_1) ⊗ Z/2) ⊕ (K^0(X_2) ⊗ Z/2)`.
  - So the obstruction fires for such a product iff some `K^0(X_i) ⊗ Z/2` is infinite.
  - We did not check whether a minimal `Z`-subshift with `K^0 ⊗ Z/2` infinite exists.

## 5. Theorem 4: the Penrose group

**The groupoid.**
- `𝒫` (ChJN arXiv:1602.04255, Section "Penrose tiling group") is the topological full group of
  the groupoid `G_𝒫` of germs of marked-vertex moves on pointed Penrose rhombus tilings up to
  translation.
- `G_𝒫` is the reduction of the translation-hull groupoid to the vertex transversal.
- Li's groupoid (L6) is Kellendonk's tiling groupoid of the classical Penrose tiling.

**Equivalence.** The two groupoids are equivalent.
- Put punctures at vertices and at tile centres. Both transversals are clopen in the groupoid
  of their union, and each meets every orbit. So both reductions are equivalent to the union
  groupoid.
- The rhombus and kite–dart versions are mutually locally derivable, so their hulls and tiling
  groupoids are equivalent as well.
- We did not verify from Li's source which classical version (L6) uses.

By (L7), `H_*(G_𝒫) ≅ Z^8, Z^5, Z, 0, ...`.

**Mod-2 homology.** By universal coefficients:
- `H_0(G_𝒫; Z/2) = (Z/2)^8`;
- `H_1(G_𝒫; Z/2) = (Z/2)^5 ⊕ Tor(Z^8, Z/2) = (Z/2)^5`;
- `H_2(G_𝒫; Z/2) = Z/2 ⊕ Tor(Z^5, Z/2) = Z/2`;
- `H_3(G_𝒫) = 0`.

**Hypotheses of Theorem 1.** Minimality and comparison hold by (L5), line 839.

**Theorem 4.**
- `H_2(D(𝒫); Z) ≅ Z ⊕ T`, where `T` is an abelian 2-group of exponent at most 4 and order
  `2^12` or `2^13`. The order depends on whether `d^2 : Z/2 -> (Z/2)^8` vanishes.
- Every `H_j(D(𝒫); Z)` is finitely generated, by Corollary 2(c).
- Rationally, Li (lines 3297–3304) gives `H_*(D(𝒫); Q) = Q` in even degrees, consistent with rank 1.

**Consequence.** No argument through integral or mod-`p` homology of `D(𝒫)` can show that
`D(𝒫)` is not finitely presented, or not of type `F_∞`.

## 6. Proposition 5: additive relation invariants are homological

**Setting.**
- `Γ = <S> <= [[Z^2 ~ X]]` (the same argument works for `Z^2 ⊕ Z/5`), with `S` finite.
- `F` is free on `S`, and `N = ker(F -> Γ)`.
- `μ` is a `Z^2`-invariant probability measure. Such a measure is `Γ`-invariant, since
  `Γ ≤ [[Z^2 ~ X]]`.

**The invariant.**
- For `w = s_k ... s_1 ∈ N` and `x ∈ X`, the points `x_j = s_j x_{j-1}` trace, in the orbit
  `Z^2 · x ≅ Z^2`, a closed lattice polygon. Let `A(w, x) ∈ (1/2) Z` be its signed area.
- `A(w, ·)` is continuous. Put `α(w) = ∫ A(w, x) dμ(x)`.

**Lemma.** `α : N -> R` is a homomorphism that vanishes on `[F, N]`.

*Proof.*
- **Additivity.** For `w_1, w_2 ∈ N` the loop of `w_1 w_2` at `x` is the loop of `w_2` at `x`
  followed by the loop of `w_1` at `w_2 x = x`, so areas add.
- **Conjugation.** The path of `u w u^{-1}` at `x` is a tail to `u^{-1} x`, then the loop of
  `w`, then the tail reversed. Tails contribute no area, so `A(u w u^{-1}, x) = A(w, u^{-1} x)`.
  Invariance of `μ` gives `α(u w u^{-1}) = α(w)`. ∎

**Consequence.**
- `α` factors through `N/[F,N]`. That group sits in
  `0 -> H_2(Γ; Z) -> N/[F,N] -> N[F,F]/[F,F] -> 0`, by Hopf's formula, and the right-hand term
  lies in `Z^{|S|}`. So `α(N)` is finitely generated whenever `H_2(Γ)` is.
- The obstruction "`α(N)` is not finitely generated, so `Γ` is not finitely presented" is
  valid, since the finitely many relators generate the image. But it cannot fire when
  `H_2(Γ)` is finitely generated.
- The same holds for every conjugation-invariant homomorphism `N -> A`. For `Γ = D(𝒫)` this
  follows from Theorem 4, and for Labbé's group from part 2.

## 7. What is left for an obstruction

Trivial-coefficient homology, and every additive invariant of relations, are finitely generated
for `D(𝒫)`. So a proof that `D(𝒫)` is not finitely presented must be nonabelian. The candidates are:
- LEF (`labbe-shift-derived-full-group-is-lef` and its periodic relator-shift criterion);
- Matui-type rigidity on defect models;
- non-spatial marked approximants;
- homology with nontrivial coefficients, which Li's theorem does not reach.

Part 2 records the same conclusion for Labbé's shift, after proving that its mod-2 cohomology is finite.
