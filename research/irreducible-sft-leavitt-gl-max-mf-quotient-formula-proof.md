---
rg: 2
id: irreducible-sft-leavitt-gl-max-mf-quotient-formula-proof
kind: route
title: Abrams–Aranda Pino gives pure infiniteness, the canonical K_1 classification gives the MF quotient, and Ara–Brustenga–Cortiñas computes K_1
target: irreducible-sft-leavitt-gl-max-mf-quotient-formula
requires:
  - leavitt-path-algebras-purely-infinite-simple-criterion
  - purely-infinite-canonical-k1-all-ranks
  - abc-leavitt-path-k-theory-exact-sequence
artifacts:
  - research/artifacts/un-k1-homology-2026-09-13-part1.md
---

Notation as in the target. Put `R = L_k(E)`.

**Step 1: `R` is a countable purely infinite simple ring.** `E` is finite and `k` countable, so `R` is countable,
and unital with unit `Σ_v p_v`. The "consequence used downstream" of
`leavitt-path-algebras-purely-infinite-simple-criterion` covers finite, cofinal, sink-free graphs with condition
(L): they meet (i)–(iii), so `R` is purely infinite simple.

**Step 2: the MF quotient is `K_1`.** By `purely-infinite-canonical-k1-all-ranks`, for every `n >= 1` the map
`κ_n : GL_n(R) → K_1(R)` is surjective, `ker κ_n = [GL_n(R), GL_n(R)] = Rad_MF(GL_n(R))`, and every homomorphism
to an MF group factors uniquely through `κ_n`. The same holds for `R^×`.

**Step 3: `K_1`.** A field is a principal ideal domain, so Corollary 7.7 of Ara–Brustenga–Cortiñas
(`abc-leavitt-path-k-theory-exact-sequence`) gives `K_1(R) = Coker(1 − N^t | K_1(k)^(E^0)) ⊕ Ker(1 − N^t | ℤ^(E^0))`.
`E` has no sinks, so no columns are removed and `N` is square. `K_1(k) = k^×`.

**Step 4: the tensor form.** `ℤ^(E^0) →(1−N^t) ℤ^(E^0) → Coker(1 − N^t | ℤ^(E^0)) → 0` is exact. `− ⊗_ℤ k^×` is
right exact, and `ℤ^(E^0) ⊗ k^× = (k^×)^(E^0)` with the map `(1 − N^t) ⊗ id` acting on exponents. That is the
action on `K_1(k)^(E^0)` in Step 3. So `Coker(1 − N^t | (k^×)^(E^0)) ≅ Coker(1 − N^t | ℤ^(E^0)) ⊗ k^×`.

**Convention.** ABC discuss two incidence conventions that differ by a transpose. For a square integer matrix,
`Coker(1 − N)` and `Coker(1 − N^t)` are isomorphic (same Smith invariants), and so are `Ker(1 − N)` and
`Ker(1 − N^t)` (free of equal rank). So the displayed isomorphism type does not depend on the convention.

**Calibration steps** (the rose, the golden-mean graph, `[[2,1],[1,2]]`) are computed in the target node. The
rose reproduces `non_mf_groups_exist.tex` Cor l.1297 for `L_k(1,d)`.

The homological remark in the target is **not** part of this derivation: it uses Cuntz's K-theory of `O_A`,
recalled rather than imported.
