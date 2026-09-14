---
rg: 2
id: banded-matrix-groups-subshift-crossed-product-proof
kind: route
title: Code the coefficient functions of finitely many banded matrices as one point of a full shift; its orbit closure is the subshift, and the orbit representation at that point is faithful
target: banded-matrix-groups-are-subshift-crossed-product-groups
requires: []
artifacts:
  - research/artifacts/sk-exact-banded-2026-09-14-part1.md
---

Notation as in the target. In `LC(Y,F_q) ⋊ Z` the convention is `ufu^{-1} = f∘σ^{-1}`, where `σ` is the shift, `(σz)_s = z_{s+1}`.

**Step 1 (the algebra of banded matrices).**
- An operator of band `w` on `F_q^{Z×m}` is uniquely a finite sum `Σ_{|j|≤w} D_j u^j` with `(D_j u^j v)(s) = D_j(s) v(s−j)` and `D_j ∈ ℓ^∞(Z, M_m(F_q))`.
- Products of such sums obey `u D u^{-1} = D(·−1)`. So the banded operators form the algebraic crossed product `M_m(ℓ^∞(Z,F_q)) ⋊ Z = M_m(ℓ^∞(Z,F_q) ⋊ Z)`, and its units are exactly the banded operators with banded inverses.
- Every function `Z → F_q` extends continuously to `βZ`, and `F_q` is discrete, so `ℓ^∞(Z,F_q) = C(βZ,F_q) = LC(βZ,F_q)`. This proves (a).

**Step 2 (coding).**
- Let `Γ = ⟨g_1,…,g_k⟩`, and write `g_i^{±1} = Σ_{|j|≤w} D^{(i,±)}_j u^j`.
- The finitely many coefficient functions give `y ∈ 𝒜^Z` over the finite alphabet `𝒜 = M_m(F_q)^N`, by `y_s = (D^{(i,±)}_j(s))_{i,±,j}`.
- Let `Y` be the closure of `{σ^n y : n ∈ Z}`. It is a transitive subshift, and `y` has dense orbit.
- Let `c^{(i,±)}_j ∈ LC(Y, M_m(F_q))` read the corresponding component of `z_0`, and put `ĝ_i^± = Σ_j c^{(i,±)}_j u^j ∈ M_m(LC(Y,F_q) ⋊ Z)`.

**Step 3 (the orbit representation).**
- Put `π_y(f)(s) = f(σ^s y)` and `π_y(u) = u`.
- It is a unital ring homomorphism `LC(Y,F_q) ⋊ Z → ℓ^∞(Z,F_q) ⋊ Z`, because `π_y(f∘σ^{-1})(s) = f(σ^{s−1}y) = π_y(f)(s−1) = (uπ_y(f)u^{-1})(s)`. It extends entrywise to `M_m`.
- `π_y(c^{(i,±)}_j)(s) = c^{(i,±)}_j(σ^s y)`, which is the component of `y_s`, namely `D^{(i,±)}_j(s)`. So `π_y(ĝ_i^±) = g_i^{±1}`.

**Step 4 (faithfulness).**
- Suppose `r = Σ_j f_j u^j ∈ M_m(LC(Y,F_q) ⋊ Z)` has `π_y(r) = 0`. Distinct powers of `u` are independent, so every `π_y(f_j) = 0`, that is, `f_j(σ^s y) = 0` for all `s`.
- The orbit of `y` is dense and `f_j` is locally constant, so `f_j = 0`. Hence `π_y` is injective.

**Step 5 (conclusion).**
- `ĝ_i^+ĝ_i^-` and `ĝ_i^-ĝ_i^+` both map to `I`, so by Step 4 they equal `I`. So `ĝ_i^± ∈ GL_m(LC(Y,F_q) ⋊ Z)` are mutually inverse.
- Put `Γ̂ = ⟨ĝ_i^+⟩`. Then `π_y|_{Γ̂}` is an injective homomorphism onto `Γ`. This proves (b).
- For (c), Step 4 applies to any `y` with dense orbit. Units map to units with banded inverses.
- Regrouping by `(t,i) ↦ mt+i` distorts distances by at most a factor `m` plus a constant, so it maps banded operators to banded operators in both directions.

**Step 6 (consequences).**
- If `X` is minimal, every orbit is dense. So `G_X ≤ GL_3(LC(X,F_2) ⋊ Z) ↪ GL^band(Z×3;F_2) ≅ GL^band(Z;F_2)`.
- Exactness passes to subgroups, since `C*_r(Λ) ⊆ C*_r(Γ)` for `Λ ≤ Γ` and exactness of C*-algebras passes to subalgebras. With (b) and (c) this gives the stated equivalence. ∎

**Model tests.**
- `Γ = ⟨u⟩` (`m = 1`): all coefficients are constant, so `Y` is a single point and `LC(Y,F_q) ⋊ Z = F_q[u^{±1}]` ✓.
- The lamplighter `⟨u, I + δ_0⟩` (the flip at site `0`): `y = …0001000…`, so `Y = orbit ∪ {0^∞}`, which is transitive and not minimal ✓. Transitivity is all (b) needs.
- A banded operator without a banded inverse (the one-sided shift on `F_q^{N}` extended by zero) is not a unit, and none is claimed.
