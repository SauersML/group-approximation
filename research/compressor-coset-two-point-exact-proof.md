---
rg: 2
id: compressor-coset-two-point-exact-proof
kind: route
title: Reduce exponents mod M and read the label off the monomial part
target: compressor-coset-two-point-exact
requires: []
---

# Reduce exponents mod M and read the label off the monomial part

**The quotient is well defined.**  Let `I_M ⊆ R` be the `F_q`-span of the
differences `x^a − x^b` with `a ≡ b (mod Mℤ^d)`.  It is an ideal
(multiplying by `x^c` translates both exponents by `c`, preserving the
congruence), and it is invariant under the monomial substitution action of
`SL_d(ℤ)` (a matrix `A` sends `a − b ∈ Mℤ^d` to `A(a−b) ∈ AMℤ^d = Mℤ^d`).
The quotient ring is `R/I_M = F_q[(ℤ/M)^d]`, the group algebra of
`(ℤ/M)^d`, a finite ring on which `SL_d(ℤ)` acts through `SL_d(ℤ/M)`.
Entrywise reduction therefore defines a homomorphism

```text
π_M : G = EL_r(R) ⋊ SL_d(ℤ)  →  Q_M := EL_r(F_q[(ℤ/M)^d]) ⋊ SL_d(ℤ/M),
```

compatible with both semidirect structures, and `Q_M` is finite.

**Item 1: `π_M(g) ∉ π_M(Γ)`.**  Every generator `e_ij(f)`, `f ∈ R_+`, of
`Γ` maps into the elementary part `N̄ := EL_r(F_q[(ℤ/M)^d])`, which is a
normal subgroup of `Q_M` with `Q_M/N̄ ≅ SL_d(ℤ/M)`.  Hence
`π_M(Γ) ≤ N̄`.  If `g = (n, A)` with `A ≠ 1` and `M` exceeds twice the
largest entry of `A`, then `A mod M ≠ 1`, so `π_M(g)` has nontrivial image
in `Q_M/N̄` and `π_M(g) ∉ N̄ ⊇ π_M(Γ)`.  A strict compressor `t ∈ SL_d(ℤ)`
qualifies: it is a nonnegative matrix of determinant 1 which is not a
permutation matrix (a nonnegative integer matrix with `Aℕ^d = ℕ^d` would
permute the coordinate rays and hence be a permutation matrix, contradicting
strictness of `tΓt⁻¹ ⊊ Γ`), so `A ≠ 1`.

**Item 3: the elementary part is exactly the image of `Γ`.**  In
`F_q[(ℤ/M)^d]` each `x̄_i` is invertible of order dividing `M`, so
`x̄^{-a} = x̄^{(M-1)a}` for every `a ∈ ℕ^d`: every monomial of the quotient
ring is the image of a monomial of `R_+`.  Since `e_ij(f₁ + f₂) =
e_ij(f₁)e_ij(f₂)`, every elementary generator `e_ij(f̄)` of `N̄` is a
product of images of generators of `Γ`.  Hence `π_M(Γ) = N̄` and
`Q_M/π_M(Γ) ≅ SL_d(ℤ/M)` as a `Q_M`-set.

**Item 2: the exact model.**  Fix `M` as in item 1 and set:

- `A := Q_M` (the underlying set), with `φ : G → Sym(A)` given by left
  multiplication through `π_M` — a unital homomorphism, hence
  `(F, ε)`-multiplicative for every window `F` and every `ε`;
- `B := Q_M/π_M(Γ)`, and `π̄ : G/Γ → B` the reduction of cosets,
  `uΓ ↦ π_M(u)π_M(Γ)`, well defined because `π_M(Γ)π_M(Γ) = π_M(Γ)`;
- `S := A`, and for `s ∈ A` the labels `j_s(x) := s^{-1}·π̄(x)` for
  `x ∈ {p, q}`, where `s^{-1}` acts by left translation on `B`.

*Distinctness.*  `π̄(p) = π_M(Γ)` and `π̄(q) = π_M(g)π_M(Γ)` differ by item
1, and left translation by `s^{-1}` is injective on `B`, so
`j_s(p) ≠ j_s(q)` for every `s ∈ A`.

*Equivariance.*  For every `g' ∈ G`, every `s ∈ A` and every `x ∈ {p,q}`
with `g'^{-1}·x ∈ {p,q}`:

```text
j_{φ(g')·s}(x) = (π_M(g')s)^{-1}·π̄(x) = s^{-1}π_M(g')^{-1}·π̄(x)
              = s^{-1}·π̄(g'^{-1}·x) = j_s(g'^{-1}·x),
```

using that `π̄` intertwines the `G`-action on `G/Γ` with the `Q_M`-action
on `B`.  The identity holds for all of `G`, with no exceptional set; in
particular all clauses of the two-point definition hold with `S = A` for
every finite `F` and every `ε > 0` at once.

**The contrast pair.**  For completeness of the correction recorded in the
claim: for `h = e_12((x_1⋯x_d)^{-1})`, choose `A_h ∈ SL_d(ℤ)` whose first
column is `-(1,…,1)` (possible since that vector is primitive) and set
`u = (1, A_h)`.  Then `u e_12(x_1) u^{-1} = e_12(x^{A_h e_1}) = h` with
`e_12(x_1) ∈ Γ`.  In any finite quotient `φ` of `G` the image `φ(Γ)` is
normal (`finite-quotient-blindness`, formalized as `compressedImage_eq`),
so `φ(h) ∈ φ(u)φ(Γ)φ(u)^{-1} = φ(Γ)`: the marked pair `(Γ, hΓ)` is
identified by **every** finite quotient, and no construction of the present
shape can separate it.
