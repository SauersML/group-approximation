---
rg: 2
id: complementary-full-idempotents-make-el-2-kazhdan-proof
kind: route
title: Grade EL_2(R) by Peirce blocks of type A_2, apply the strong-grading criterion, and get relative (T) from the corner ring eRe
target: complementary-full-idempotents-make-el-2-kazhdan
requires:
  - strongly-root-graded-groups-have-kazhdan-root-unions
  - elementary-linear-semidir-pair-relative-t
artifacts:
  - research/artifacts/sk-el2-idempotent-grading-2026-09-13-part1.md
---

Full derivation: `research/artifacts/sk-el2-idempotent-grading-2026-09-13-part1.md` §1. Outline:

1. **Blocks.** `E_1 = eE_11`, `E_2 = eE_22` and `E_3 = (1−e)I_2` are orthogonal idempotents of `M = M_2(R)`, and each is full.
   Put `Y_AB = I + E_AME_B`. For `x ∈ E_AME_B` and `y ∈ E_BME_C`, `yx = 0`, so `[I+x, I+y] = I+xy`.
2. **The grading** (Lemma 2).
   - `Y_AB ⊆ EL_2(R)`. Diagonal pieces are single commutators of elementary matrices.
   - `EL_2(R) = ⟨Y⟩`. The piece `e_12((1−e)r(1−e))` is a product of commutators from `Y_32` and `Y_23`.
   - The commutator axiom holds, and `[Y_AB, Y_BC] = Y_AC` because `E_B` is full. So the `A_2`-grading is strong, and
     `strongly-root-graded-groups-have-kazhdan-root-unions`(a) makes `∪Y_AB` a Kazhdan subset.
3. **Corner.** `S = eRe` is finitely generated (Lemma 3: insert `1 = Σ a_t e b_t` between the letters of a word).
4. **Relative (T)** (Lemma 4).
   - *Column roots.* `ρ(A) = (1−e)I + A` identifies `⟨Y_12, Y_21⟩` with `EL_2(S)`, and `Y_13Y_23` with `M_2(L)`, where `L = eR(1−e)`
     and `EL_2(S)` acts on the columns. `L` is a finitely generated left `S`-module.
     - `EL_2(S) ⋉ (S²)^{2m}` maps onto `⟨Y_12,Y_21⟩ ⋉ Y_13Y_23`.
     - Each factor `EL_2(S) ⋉ S²` has relative (T) (`elementary-linear-semidir-pair-relative-t`). Finitely many factors combine by the triangle
       inequality, and relative (T) pushes forward along the homomorphism.
   - *Row roots.* `Y_31`, `Y_32` go through the isomorphism `g ↦ (g^T)^{-1}`, `GL_2(R) → GL_2(R^op)`, and the column case for `R^op`.
   - *Roots `(1,2)`, `(2,1)`.* `Y_12 ⊆ (Y_13Y_32Y_13Y_32)^{m'}` because `E_3` is full, so relative (T) follows.
5. **(T).** `κ(G, ∪Y) > 0` and `(G, ∪Y)` has relative (T), so `G` has a finite Kazhdan set (Ershov–Jaikin-Zapirain: "clear from definitions").

Firewall. `EL_2(R)` lacks (T) for infinite commutative `R`, and for `R` surjecting onto `Z` or `F[t]` (the EJZK footnote, quoted in
the artifact §0). The hypothesis excludes both.
