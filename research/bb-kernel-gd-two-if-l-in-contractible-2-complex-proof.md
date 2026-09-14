---
rg: 2
id: bb-kernel-gd-two-if-l-in-contractible-2-complex-proof
kind: route
title: Run the Bestvina--Brady Morse sweep with copies of a contractible 2-complex in place of the cones on L
target: bb-kernel-gd-two-if-l-lies-in-contractible-2-complex
requires: []
artifacts:
  - research/artifacts/hl-eg-bestvina-brady-2026-09-14.md
---

**Imports from Bestvina--Brady, Invent. Math. 129 (1997), verbatim** (artifact §1).
- **Lemma 2.3 (p. 448).** "If J ⊂ J′ ⊂ R are connected and X_J′ \ X_J contains no vertices of
  X, then X_J ↪ X_J′ is a homotopy equivalence."
- **Lemma 2.5 (p. 449).** If `J ⊂ J′` are closed connected intervals with a common infimum and
  `J′ \ J` contains exactly one critical value `r`, then "X_J′ is homotopy equivalent to X_J with
  the copies of Lk↓(v, X) (v a vertex with f(v) = r) coned off". The proof constructs "a strong
  deformation retraction of X_J′ onto X_J with the cones attached". The common-supremum version
  uses `Lk↑`.
- **p. 454.** The Morse function `f: X → R` is `φ`-equivariant, "with the ↑-links and ↓-links
  all isomorphic to L".

**Step 0: setup.**
- **The action.** `G_L` acts freely and cellularly on the CAT(0) cube complex `X` by deck
  transformations, and `H_L` preserves `f`. `G_L` is torsion-free, so an element stabilizing a
  cell setwise has a power fixing a vertex, hence is trivial. So `H_L` permutes cells freely.
- **The sweep.** `f(X^0)` is discrete and unbounded in both directions. Fix `t ∉ f(X^0)`.
  - List the critical values above `t` increasingly as `a_1 < a_2 < …`, and those below `t`
    decreasingly as `b_1 > b_2 > …`.
  - Set `J_0 = {t}` and add `a_1, b_1, a_2, b_2, …` alternately: `J_1 = [t, a_1]`,
    `J_2 = [b_1, a_1]`, and so on.
  - Then `X = ∪_k X_(J_k)`, and `V_k`, the vertices at the value `r` added at step `k`, is a free
    `H_L`-set.
- **Upward step** (the downward step is the mirror image). Suppose `J_k = [b, r]` and
  `J_(k−1) = [b, a]` with `a < r`. Choose `0 < δ < r − a` and put `J⁻ = [b, r − δ]`.
  - `X_(J⁻) \ X_(J_(k−1))` contains no vertices. By Lemma 2.3, `ι: X_(J_(k−1)) ↪ X_(J⁻)` is a
    homotopy equivalence.
  - By the proof of Lemma 2.5, `X_(J_k)` strong deformation retracts onto
    `T_k = X_(J⁻) ∪ ∪_(v ∈ V_k) C_v`. Here `C_v` is the part of the cells having `v` as their
    maximum that lies in `f^(−1)[r − δ, r]`.
  - Each `C_v` is a cone with apex `v` on a copy of `Lk↓(v, X) ≅ L`, embedded in `X_(J⁻)` by some
    `α_v: L → X_(J⁻)`. The pieces are defined from the cells at `v`, so `h C_v = C_(hv)` and
    `α_(hv) = h α_v` for `h ∈ H_L`.
  - So `T_k` is the mapping cone of `⊔ α_v`, sitting in `X_(J_k)`, and `T_k ↪ X_(J_k)` is a
    homotopy equivalence.

**Step 1: induction.** Put `Ŷ_0 = X_t`, a 2-dimensional free `H_L`-CW complex, and
`e_0 = id: Ŷ_0 → X_(J_0)`. Suppose `Ŷ_(k−1)` is a 2-dimensional free `H_L`-CW complex with an
`H_L`-equivariant homotopy equivalence `e_(k−1): Ŷ_(k−1) → X_(J_(k−1))`.
- **Attaching maps.** In each `H_L`-orbit of `V_k` pick `v_0`. Using a homotopy inverse of
  `ι e_(k−1)` and cellular approximation, choose a cellular `β_(v_0): L → Ŷ_(k−1)` and a homotopy
  `G_(v_0): L × [0,1] → X_(J⁻)` from `ι e_(k−1) β_(v_0)` to `α_(v_0)`. For `h ∈ H_L` set
  `β_(hv_0) = h β_(v_0)` and `G_(hv_0) = h G_(v_0)`.
- **New stage.** Let `Ŷ_k = Ŷ_(k−1) ∪_(⊔ β_v) ⊔_(v ∈ V_k) Z_v`, with `Z_v` copies of `Z` glued
  along `L ⊆ Z_v`. It is a 2-dimensional CW complex. `H_L` acts on it (`h: Z_v → Z_(hv)`), freely
  on cells.
- **Extending the map.** Let `Cone′(L) = L × [0,2] / L × {2}`. Define
  `ψ_(v_0): Cone′(L) → X_(J_k)` by `G_(v_0)` on `L × [0,1]` and by the cone `C_(v_0)` on
  `L × [1,2]/~`, with `L × {1}` going to `α_(v_0)` and `L × {2}` to `v_0`.
  - `(Z, L)` is a CW pair and `Cone′(L)` is contractible, so `L ≅ L × {0} ↪ Cone′(L)` extends to
    `ρ: Z → Cone′(L)`.
  - Set `e_k = ι e_(k−1)` on `Ŷ_(k−1)` and `e_k = h ψ_(v_0) ρ` on `Z_(hv_0)`. These agree on `L`,
    and `e_k: Ŷ_k → X_(J_k)` is `H_L`-equivariant.

**Step 2: e_k is a homotopy equivalence.**
- **Comparison with a pushout.** Map the diagram `Ŷ_(k−1) ← ⊔L ↪ ⊔Z_v` to the diagram
  `X_(J⁻) ← ⊔L ↪ ⊔Cone′(L)`, with attaching maps `ι e_(k−1) β_v`. The vertical maps are
  `ι e_(k−1)`, the identity, and `ρ`. All are homotopy equivalences, and both right-hand maps are
  cofibrations. By the gluing theorem, `Ŷ_k` is homotopy equivalent to the pushout `P`.
- **From P to X_(J_k).** Using `G_v` on the collars maps `P` to `T_k`. This is a homotopy
  equivalence rel `X_(J⁻)`, because mapping cones of homotopic maps are equivalent (e.g. Hatcher,
  Proposition 0.18). Then `T_k ↪ X_(J_k)` is a homotopy equivalence by Step 0.
- **Conclusion.** The composite `Ŷ_k → P → T_k ↪ X_(J_k)` is `e_k`, so `e_k` is a homotopy
  equivalence.

**Step 3: colimit.** `Ŷ = ∪_k Ŷ_k` is a 2-dimensional CW complex with a free cellular `H_L`-action,
and `e = ∪ e_k: Ŷ → X`.
- Compact sets and homotopies lie in finite stages on both sides, since `f` is bounded on compact
  sets, and the stage maps commute with the inclusions. So
  `π_i(Ŷ) = colim π_i(Ŷ_k) ≅ colim π_i(X_(J_k)) = π_i(X) = 0`.
- By Whitehead's theorem `Ŷ` is contractible. So `Ŷ / H_L` is a 2-dimensional `K(H_L,1)`.
- For acyclic `L` with `π_1(L) ≠ 1`, `H_L` has cohomological dimension 2 (Step 1 of
  `acyclic-nonaspherical-l-dichotomy-proof`), so the geometric dimension is 2.

**Trust surface.**
- **Imported.** Lemmas 2.3 and 2.5 and the link statement on p. 454, together with the shape of
  the retract in the proof of Lemma 2.5 (cones on link copies at level `r − δ`, defined cell by
  cell).
- **Standard, recalled and not pinned.** Cellular approximation, extension into contractible
  targets, the gluing theorem, invariance of attaching maps under homotopy, and Whitehead's
  theorem.
