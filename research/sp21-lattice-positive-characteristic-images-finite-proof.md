---
rg: 2
id: sp21-lattice-positive-characteristic-images-finite-proof
kind: route
title: An infinite image has an eigenvalue off the unit circle at some local place, but the building action has a fixed point
target: sp21-lattice-positive-characteristic-images-finite
requires: []
---

**Imported inputs (statements; the sources were not re-read in this pass).**

- **(S) Schur.** A finitely generated torsion subgroup of `GL_m(K)` is finite.
- **(TL) Tits' lemma** (J. Tits, *Free subgroups in linear groups*, J. Algebra 20,
  1972, Lemma 4.1). Let `K` be a finitely generated field and `λ in K` not a root
  of unity. Then there are a locally compact field `k` and an embedding
  `σ: K -> k` with `|σ(λ)| != 1`. In characteristic `p`, `k` is nonarchimedean.
- **(GS) Gromov--Schoen** (Publ. IHES 76, 1992), nonarchimedean superrigidity.
  A cocompact lattice in `Sp(n,1)`, `n >= 2`, or `F_4^(-20)` fixes a point in
  every isometric action on a locally finite Euclidean building. **Trust
  surface:** this form is used for the building of `SL_m(k)` over a local field
  of positive characteristic. That building is locally finite because the
  residue field is finite.
- **(T) Kostant.** `Γ` has property (T), so `Γ^ab` is finite.

**Proof.**
1. **Reduce to one bad element.** `Γ` is finitely generated, so we may take `K`
   finitely generated. Suppose `ρ(Γ)` is infinite. By (S) some `A = ρ(γ)` has
   infinite order.
2. **Find an eigenvalue that is not a root of unity.** If every eigenvalue of `A`
   were a root of unity, some power `A^N` would be unipotent. A unipotent matrix
   in characteristic `p` satisfies `(1+X)^(p^j) = 1 + X^(p^j) = 1` once
   `p^j >= m`, so `A` would have finite order. Hence some eigenvalue `λ` of `A` is
   not a root of unity. Enlarge `K` by `λ`; it is still finitely generated.
3. **Move to a local field.** By (TL) there are a nonarchimedean local field `k`
   and an embedding `σ: K -> k` with `|σ(λ)| != 1`. Replacing `γ` by `γ^-1` gives
   `|σ(λ)| > 1`. Put `ρ_k = σ ∘ ρ: Γ -> GL_m(k)`.
4. **Control the determinant.** `det ∘ ρ_k` factors through the finite group
   `Γ^ab`. So `|det ρ_k(δ)| = 1` for every `δ`.
5. **Apply the fixed point.** `PGL_m(k)` acts by isometries on the locally finite
   Euclidean building of `SL_m(k)`. By (GS) the image of `Γ` fixes a point `x`.
   The stabilizer of `x` in `PGL_m(k)` is compact. The ratios `|μ_i/μ_j|` of
   the eigenvalues of a lift are well defined and continuous on `PGL_m(k)`. So
   they are bounded along the powers of any element of a compact subgroup, and
   `|μ_i/μ_j|^N` bounded for all `N` forces `|μ_i/μ_j| = 1`. Hence for every
   `δ in Γ`, all eigenvalues of `ρ_k(δ)` have one common absolute value.
6. **Conclude.** By step 4 that common value is `1`. This contradicts
   `|σ(λ)| > 1` at `δ = γ`. So `ρ(Γ)` is finite. `QED`
