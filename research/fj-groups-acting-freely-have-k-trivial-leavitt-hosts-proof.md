---
rg: 2
id: fj-groups-acting-freely-have-k-trivial-leavitt-hosts-proof
kind: route
title: Shrink the family to finite-by-cyclic subgroups (Davis–Quinn–Reich); free finite orbits give matrix rings over LC(D, L), and finite-by-Z orbits give skew Laurent rings over them, all K-trivial
target: farrell-jones-groups-acting-freely-have-k-trivial-leavitt-hosts
requires:
  - crossed-product-rings-inherit-fjc-with-additive-coefficients
  - fj-family-reduces-to-finite-by-cyclic-with-coefficients
  - regular-coherent-laurent-coefficients-kill-twisted-nil-terms
  - ara-cortinas-leavitt-tensor-k-theory-vanishes
  - cantor-crossed-product-leavitt-tensors-are-k-trivial
artifacts:
  - research/artifacts/fjc-crossed-product-leavitt-hosts-2026-09-16.md
  - experiments/leavitt-kh-2026-09-17/dqr-1002.3702-excerpts.txt
---

Notation as in the target. For a compact zero-dimensional `Y`, put
`R_Y = LC(Y, L)`.

The artifact lemmas below are the ones used by route
`cantor-crossed-product-leavitt-tensors-are-k-trivial-proof`, Part 1. They are
stated there for an arbitrary compact zero-dimensional space. Lemmas 4.2 and 4.3
rest on `ara-cortinas-leavitt-tensor-k-theory-vanishes`.

**Step 1: crossed product.** By artifact Lemma 4.1 (route steps 1 and 2),
`B ⊗ L ≅ R_X ⋊ Λ`. This is a Bartels–Reich crossed product with `τ ≡ 1`, and
`Λ` acts on `R_X` by `F -> F ∘ g^(-1)`.

**Step 2: assembly over `fbc`.** Let `A` be the additive `Λ`-category of
`crossed-product-rings-inherit-fjc-with-additive-coefficients`.
- By part 2 of that claim and the hypothesis on `Λ`, the map
  `H_n^Λ(E_VCyc Λ; K_A) -> K_n(R_X ⋊ Λ)` is bijective.
- By `fj-family-reduces-to-finite-by-cyclic-with-coefficients`, the
  map `H_n^Λ(E_fbc Λ; K_A) -> K_n(R_X ⋊ Λ)` is bijective for every `n`.
- By part 1 of that claim, the coefficients are
  `H_n^Λ(Λ/H; K_A) ≅ K_n(R_X ⋊ H)`.

**Step 3: finite orbits.** Let `F ≤ Λ` be finite. It acts freely by hypothesis.

*(a) Clopen fundamental domain.*
- For each `x ∈ X`, the points `hx` for `h ∈ F` are distinct.
- Since `X` is Hausdorff and zero-dimensional and `F` is finite, `x` has a
  clopen neighbourhood `W_x` with `hW_x ∩ W_x = ∅` for every `h ≠ 1`.
- By compactness, finitely many of them, `W_1, …, W_k`, cover `X`.
- Put `D_1 = W_1` and `D_j = W_j \ F·(D_1 ∪ … ∪ D_(j-1))`, and let `D = ⋃ D_j`.
  Each `D_j` is clopen, because `F·(clopen)` is a finite union of clopens.
- `D` meets each orbit at most once:
  - `D_j ⊆ W_j` meets each orbit at most once;
  - `D_j` misses the orbits already met by `D_1, …, D_(j-1)`.
- `D` meets each orbit at least once. Take the least `j` with `Fx ∩ W_j ≠ ∅`.
  Then `Fx ∩ W_j ⊆ D_j`, because the orbit was not met earlier.
- So `X = ⊔_(h∈F) hD`.

*(b) Matrix units.*
- Put `e_(h,h') = 1_(hD) u_(h h'^(-1))` in `S = R_X ⋊ F`.
- Using `u_g 1_W = 1_(gW) u_g`:
  `e_(h,h') e_(k,k') = 1_(hD) 1_(h h'^(-1) k D) u_(h h'^(-1) k k'^(-1))`.
- This is `δ_(h',k) e_(h,k')`, because `h'^(-1)kD ∩ D = ∅` unless `h' = k`.
- Also `Σ_h e_(h,h) = Σ_h 1_(hD) = 1`.
- The corner is `e_(1,1) S e_(1,1) = ⊕_g 1_D R_X 1_(gD) u_g`. It equals `R_D`,
  since `1_D 1_(gD) = 0` for `g ≠ 1`.
- A unital ring with a complete system of `n × n` matrix units is `M_n` of its
  corner. So `S ≅ M_|F|(R_D)`.

*(c) K-triviality.*
- `K_n(R_D) = 0` for all `n` (artifact Lemma 4.2, applied to `D`).
- Non-connective `K`-theory is Morita invariant, so `K_n(S) = 0` for all `n`.

*(d) Regular coherence.*
- `R_D[Z^m]` is regular coherent on both sides (artifact Lemma 4.3, applied to
  `D`).
- `S[Z^m] = M_|F|(R_D[Z^m])`.
- The Morita equivalence `Mod-T ≃ Mod-M_n(T)` is an equivalence of abelian
  categories. It preserves finitely presented modules, finitely generated
  projective modules and exact sequences.
- So "every finitely presented module has a finite resolution by finitely
  generated projectives" passes from `T = R_D[Z^m]` to `M_n(T)`. Hence
  `S[Z^m]` is regular coherent for every `m >= 0`.

**Step 4: finite-by-Z orbits.** Let `V ∈ fbc` be infinite, with finite normal
subgroup `F` and `V/F ≅ Z`.
- Pick `t ∈ V` mapping to a generator. Then `V = ⊔_k F t^k`, so `R_X ⋊ V` is
  free as a left `S`-module on the `u_t^k`, where `S = R_X ⋊ F`.
- `u_t` is a unit and `α(s) = u_t^(-1) s u_t` preserves `S`, because `t`
  normalises `F` and `R_X`.
- So `R_X ⋊ V = S_α[t, t^(-1)]`, with `s u_t = u_t α(s)`.
- By Step 3(c) and (d), `regular-coherent-laurent-coefficients-kill-twisted-nil-terms`
  applies. It gives `K(R_X ⋊ V) ≃` the mapping torus of `K(α^(-1))` on
  `K(S) ≃ *`, which is contractible.

**Step 5: conclusion.**
- Every isotropy group of `E = E_fbc Λ` lies in `fbc`. By Steps 3 and 4, the
  Or(Λ)-spectrum `K_A` is contractible at every such orbit.
- `E` is the colimit of its skeleta `E_n`. Each pushout
  `⊔ Λ/H_i × S^(n-1) -> ⊔ Λ/H_i × D^n` changes
  `map_Λ(-, E_n)_+ ∧_(Or Λ) K_A` by a cofibre that is a wedge of
  `Σ^n K_A(Λ/H_i)`. That cofibre is contractible.
- Homotopy groups commute with the sequential colimit. So
  `H_*^Λ(E; K_A) = 0`, and by Step 2, `K_n(B ⊗ L) = 0` for every `n ∈ Z`. ∎

**Where the hypotheses enter.**
- Freeness is used only in Step 3(a), for finite subgroups.
- The Farrell–Jones hypothesis is used only in Step 2.
- No finite generation of `Λ` is used.
