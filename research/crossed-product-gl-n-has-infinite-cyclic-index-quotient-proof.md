---
rg: 2
id: crossed-product-gl-n-has-infinite-cyclic-index-quotient-proof
kind: route
title: Proof via the compression of the orbit representation to a half orbit
target: crossed-product-gl-n-has-infinite-cyclic-index-quotient
requires: []
---

**Orbit representation.** Fix `x ∈ X`, and let `V = ⊕_(m ∈ Z) k δ_m` (finitely supported sequences). Define `π(f) δ_m = f(T^m x) δ_m` and `π(u) δ_m = δ_(m+1)`.
This is a unital ring homomorphism `R → End_k(V)`, since
`π(u) π(f) π(u)^(-1) δ_m = f(T^(m−1) x) δ_m = π(f∘T^(-1)) δ_m`.
Apply `π` entrywise to get `M_n(R) → End_k(V^n)`. If every entry of `g ∈ M_n(R)` involves only powers `u^j` with `|j| ≤ w`, then `π(g)` maps `δ_m ⊗ k^n` into the span of the `δ_(m') ⊗ k^n` with `|m' − m| ≤ w`.

**Compression.** Let `P` be the projection of `V^n` onto `V_+^n`, where `V_+ = ⊕_(m ≥ 0) k δ_m`. For `g, h ∈ M_n(R)`,
`P π(gh) P − (P π(g) P)(P π(h) P) = P π(g) (1−P) π(h) P`.
If `h` has exponents bounded by `w`, then `(1−P) π(h) P` has range inside `⊕_(−w ≤ m < 0) δ_m ⊗ k^n`, so the difference has rank at most `nw`.

**Fredholm index.** For `g ∈ GL_n(R)`, put `A = P π(g) P` and `B = P π(g^(-1)) P` on `V_+^n`. Then `AB − 1` and `BA − 1` have finite rank.
- `ker A ⊆ ker(BA)`, which is finite-dimensional because it lies in the range of `BA − 1`.
- `range A ⊇ range(AB)`, which has finite codimension.
So `A` has finite-dimensional kernel and cokernel.
Put `ind(g) = dim ker A − dim coker A`. Standard linear algebra over any field shows:
- the index of a composite of such maps is the sum of the indices;
- a finite-rank perturbation does not change the index.
With the rank estimate above, this gives `ind(gh) = ind(g) + ind(h)`, so `ind` is a homomorphism.

**Values.**
- For `i ≠ j` and `r ∈ R`, `P π(e_ij(r)) P = 1 + (P π(r) P) E_ij`. It is invertible, with inverse `1 − (P π(r) P) E_ij`, because `E_ij^2 = 0`. So its index is `0`.
- `P π(diag(u,1,…,1)) P` is the unilateral shift `δ_m ↦ δ_(m+1)` on the first summand `V_+` and the identity on the others. It is injective, and its cokernel is spanned by `δ_0` in the first summand. So its index is `−1`.

**Consequences.**
- A Kazhdan group has finite abelianization, and `GL_n(R)` maps onto `Z`. So `GL_n(R)` has no property (T).
- For `n ≥ 2`, `ker(ind)` is a proper normal subgroup containing the nontrivial group `EL_n(R)`.
- If `X` is minimal, then `Z(R) = k`: a central element is invariant and locally constant, and it is constant by minimality, as in the note l.110–113. So `Z(GL_n(R)) = k^× I_n`. For `c ∈ k^×`, `P π(c I_n) P = c·1` is invertible, so it has index `0`. Then `ind` descends to `GL_n(R)/Z ↠ Z`.

**Model test.** For `X = {a^∞}`, `R = k[u, u^(-1)]` and `ind(g)` is the winding number of `det g`. For example, `ind(diag(u,1)) = −1`, and `ind(e_12(r)) = 0`.
