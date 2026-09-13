# EX review, groups: part 18. The Atiyah–determinant tester and its permanence, norm-two matrices, the Penrose group, citation imports

Lane `ex-verify-groups`, 2026-09-13, ~03:10 CDT. Index: `ex-review-groups-2026-09-12.md`.

## 18.1 ex-atiyah-torsion-free: `algebraic-atiyah-with-determinant-closed-under-colimits` (requires: []). PASS

This node was established 2026-09-11, before EX. It is reviewed because the tester below and
ex-atiyah-base-change-td2 build on it.

- **`F_T(λ)`.** It is the largest dimension of a submodule on which `T` contracts by `λ`. Such a submodule
  meets the range of `χ_(λ,∞)(|T|)` only in `0`, so projecting it onto the complementary range is injective.
- **Subgroups.** The two spectral measures agree, since `δ_e` lies in the copy of `ℓ^2(H)` for the trivial coset.
- **Colimits.** A torsion element dies at a stage, so the colimit is torsion-free.
- **Det along colimits.** Lück, arXiv:2102.04549v2, Remark 3.11. An import, not re-read.
- **Moments.** The identity coefficients of `trace((A_j A_j^*)^k)` stabilize, and supports are uniformly
  bounded, so `μ_j -> μ` weakly.
- **Restriction of scalars.**
  - `P ρ(x) P^-1 = diag_s σ_s(x)`.
  - In (i), take `T = ⊕_s r_(σ_s(A_j))` and `T' = r_(M_j)`, with `c = ||P|| ||P^-1||`. So
    `F_(A_j)(λ) - F_(A_j)(0) <= F_(M_j)(cλ) - F_(M_j)(0)`.
  - (iii) splits `log det >= 0` at `λ`, with total dimension `md`.
- **The atom.** The closed-set bound `limsup μ_j({0}) <= μ({0})`, the open-set bound on `(-1, λ^2)`, and
  `λ -> 0` give `μ({0}) = lim μ_j({0})`.

## 18.2 `algebraic-atiyah-and-determinant-one-group-tester`. PASS

- **Equivalence.** From 18.1 and item 6 of `two-generator-fp-torsion-free-master-tester`, checked at that item:
  `E ∈ C` ⇒ `U ∈ C` ⇒ every finitely generated recursively presented torsion-free group is in `C` ⇒ every
  torsion-free group is in `C`.
- **Dichotomy.**
  - The integers `μ_j({0})` are eventually `<= N`, and the open-set liminf is `>= N + η`.
  - So `μ_j((0, λ^2)) >= η/2`, which exceeds the Step 5(iii) bound.
  - Hence `Det` fails for `ρ(A_j)` over a stage `K_j <= E`, and that stage is not sofic.
- **`torsion-free-directed-colimit-recursively-presented`, checked.**
  - Universal torsion-free quotients are functorial.
  - `bq = id_G` because the colimit maps `a_i` are jointly epimorphic. `qb = id_C` because the `q_i` are
    surjective and the `c_i` are jointly epimorphic.
  - Chiodo, Corollary 3.4 and Proposition 3.8, not re-read.
- **Import, pre-EX.** The universal container: `E` is two-generator, finitely presented, torsion-free,
  contains every finitely generated recursively presented torsion-free group, and is not sofic.

## 18.3 ex-determinant-monster: `norm-two-integral-matrices-reduce-to-virtually-cyclic-groups`. PASS. Import title corrected

- **Balls.** Compressions are cyclotomic, and the induced subgraph on a ball is connected.
- **Linear growth.**
  - Each ball is contained in a maximal cyclotomic matrix (McKee–Smyth Theorem 3).
  - Tessellation balls have `<= 4r + 2` vertices. Every other maximal matrix has `<= 16`, including `(2)` and
    `[[0,2],[2,0]]`.
- **Stabilizers.** They act freely, with one orbit per level. Švarc–Milnor applies, and linear growth gives
  finite or virtually `Z`.
- **Consequences.**
  - The root spectral measure decomposes over components, and the Serre class is convex.
  - Thom's Galois balance and Kronecker give the eigenvalues.
  - Lück approximation holds for residually finite virtually cyclic groups.
- **Title correction.** The cited `cyclotomic-integer-matrices-classified` had a title that omitted the
  `1 × 1` matrix `(2)`. That matrix is contained in no charged signed graph and not in `[[0,2],[2,0]]`. The
  body quoted Theorem 3 correctly, and the consumer handled the case. The title is corrected forward, landed
  with this part.

## 18.4 ex-fp-simple-sofic: `penrose-tiling-group-is-an-amenable-orbit-full-group`. PASS

- **Freeness.** If `a ∈ P` fixes `x̃` modulo `Lat`, projecting to `C` gives `a ∈ Lat`.
- **Measure.** The lines of `L` form a countable, null, invariant union, and off it `Q̄` is a bijection. Full
  support follows from basic polygons.
- **Item 3.** Continuous cocycles have finite range, so `amenable-orbit-full-group-subgroups-are-sofic` applies
  (parts 2 and 7).
- **Trust surface.** ChJN TeX readings, for `Λ ≅ Z^2 ⊕ Z/5` and `𝒫 ≅ [[Λ ~ X]]`.

## 18.5 Citation imports, at citation level only

None of these was re-read against the PDF here.

- **`strong-atiyah-passes-to-locally-indicable-extensions`** and **`one-relator-groups-satisfy-strong-atiyah`**
  (Jaikin-Zapirain–López-Álvarez, Proposition 6.5 and Corollary 1.3). "A nonsofic one-relator group is
  torsion-free and locally indicable" follows from Wise and Brodskii, as printed.
- **`thompson-f-character-simplex`** (Dudko–Medynets, Corollary 3.3(2)). Consistent with the `G_(n,r)`
  corollary in `thompson-v-character-simplex`.
- **`almost-commuting-permutations-are-near-commuting`** (Arzhantseva–Păunescu, Main Theorem with
  Definition 3.2).
- **`smith-serre-measures-are-conjugate-limits`** (Smith, Theorem 1.5). The node correctly separates Smith's
  integrand, which runs over zero sets, from the graph's Serre class.
- **`cyclotomic-integer-matrices-classified`** (McKee–Smyth, Theorems 1–3). Body correct; title corrected (18.3).
- **Not reviewed here.** `bleak-quick-finite-presentations-of-thompson-v` and the Leavitt presentation nodes.
  Presentation completeness belongs to ex-verify-presentation.

## 18.6 Status at tip 863ff0446b

- **Famous-root fixpoint.** Only the four known flips: the Pestov 9.1 answer (part 1) and three peer flips
  outside scope.
- **Other roots.** All compute open: `torsion-free-sofic-exact-mf-radical-over-z`,
  `fp-simple-group-in-amenable-orbit-full-group`, `labbe-shift-derived-full-group-is-finitely-presented`,
  `titz-witzel-kernel-nonsofic`, `nonsofic-one-relator-group` and `hyperlinear-fp-infinite-simple-kazhdan-group`.
