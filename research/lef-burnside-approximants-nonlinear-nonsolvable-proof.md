---
rg: 2
id: lef-burnside-approximants-nonlinear-nonsolvable-proof
kind: route
title: Transfer laws to the limit, then kill nilpotent, solvable and bounded-degree approximants with Zelmanov and Malcev
target: lef-burnside-approximants-are-nonlinear-and-nonsolvable
requires:
  - restricted-burnside-finiteness
  - finite-nilpotent-groups-satisfy-local-restricted-burnside
  - finitely-generated-linear-groups-are-residually-finite
---

Notation as in the target; `F = F_m` with basis `x_i`, and `K = ker(F -> L)`.

**Clause 0.** Let `ω` hold in `Q_n` for `n` in an infinite set `J`. Take elements
`g_1, ..., g_j ∈ L` with representative words `u_1, ..., u_j`. The word
`ω(u_1, ..., u_j)` has some length `r`. For large `n ∈ J` it is trivial in `Q_n`
(the law holds there), and by agreement on words of length `<= r` it is trivial
in `L`. So `ω(g_1, ..., g_j) = 1`.

**Clause 1.** `L` is infinite, so `|B_r(L)| -> ∞`. For large `n`, distinct
elements of `B_r(L)` have distinct images in `Q_n` (for words `u, v` of length
`<= r`, `u^{-1}v` has length `<= 2r`, and agreement on words of length `<= 2r`
applies). So `|Q_n| >= |B_r(L)|` for large `n`.

**Clause 2.** Let `R_nil = R_nil(m,N)` be the radius of clause 1 of
`finite-nilpotent-groups-satisfy-local-restricted-burnside`. For words `h` of
length `<= R_nil`, `h^N` is trivial in `L` and has length `<= N R_nil`. So for
all large `n`, the words of length `<= R_nil` in `Q_n` satisfy the law. A
nilpotent such `Q_n` is a quotient of `R(m,N)` by that clause, so
`|Q_n| <= |R(m,N)|`, which is finite (`restricted-burnside-finiteness`). By
clause 1 only finitely many `Q_n` can do this.

**Clause 3.** Let `δ_0(y) = y` and
`δ_ℓ(y_1, ..., y_{2^ℓ}) = [δ_{ℓ-1}(y_1, ..., y_{2^{ℓ-1}}), δ_{ℓ-1}(y_{2^{ℓ-1}+1}, ..., y_{2^ℓ})]`.
A group is solvable of derived length `<= ℓ` iff `δ_ℓ = 1` is a law in it. If
infinitely many `Q_n` satisfy it, clause 0 makes `L` solvable of derived length
`<= ℓ`. A finitely generated solvable group of finite exponent is finite:
- `L/L'` is a finitely generated abelian group of finite exponent, hence finite;
- so `L'` has finite index, hence is finitely generated (Schreier), is periodic,
  and has smaller derived length;
- induct on derived length.

This contradicts `L` infinite.

**Clause 4.** Suppose that for `n` in an infinite set `J`, `Q_n` has a faithful
representation of dimension `<= d` over a field `k_n`. Padding with identity
blocks, `Q_n ≤ GL_d(k_n)`.
- **Ultraproduct.** Let `U` be a nonprincipal ultrafilter on `J` and
  `k = ∏_U k_n`, a field. Sending a class `[(g_n)]` to the matrix of classes of
  entries is an injective homomorphism `∏_U GL_d(k_n) -> GL_d(k)`: it is
  multiplicative entrywise, and the determinant of the image is the class of the
  nonzero determinants.
- **The limit embeds.** Let `ψ: F -> ∏_U Q_n` send `x_i` to `[(s_i^(n))]`. A word
  `w` lies in `ker ψ` iff `{n ∈ J : w(s^(n)) = 1} ∈ U`. By convergence that set is
  cofinite in `J` when `w ∈ K`, and finite when `w ∉ K`. Nonprincipal
  ultrafilters contain every cofinite subset and no finite one, so `ker ψ = K`.
  Hence `L ≅ ψ(F) ≤ GL_d(k)`.
- **Finiteness.** `L` is a finitely generated linear group over a field, hence
  residually finite (`finitely-generated-linear-groups-are-residually-finite`).
  Each finite quotient of `L` is an `m`-generated group of exponent dividing `N`,
  hence a quotient of `R(m,N)` (clause 2 of `restricted-burnside-finiteness`).
  So `ker(F -> R(m,N))` maps into every finite-index normal subgroup of `L`. Their
  intersection is trivial, so `L` is a quotient of `R(m,N)`, hence finite.

This contradicts `L` infinite. ∎
