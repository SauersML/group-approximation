---
rg: 2
id: equivariant-ehs-sign-involution-proof
kind: route
title: Permutation stages are cohomologically trivial and H1 passes to colimits
target: equivariant-ehs-fails-for-sign-involutions
requires: []
artifacts:
  - research/artifacts/stw99-lii-equivariant-ehs-obstruction-2026-08-30.md
---

**The witness is a dimension group.**  Positivity is decided by the
functional `ℓ(x,y,z) = x + θy` alone.  Unperforation is immediate.
Interpolation: given `a_i ≤ b_j` (`i,j ∈ {1,2}`), if some `a_i` equals
some `b_j` that element interpolates; otherwise
`max ℓ(a_i) < min ℓ(b_j)` and density of `Z + θZ` in `R` supplies `c`
with `ℓ` strictly between, so `a_i ≤ c ≤ b_j`.  `u = (1,0,0)` is an
order unit since `ℓ(u) > 0` and multiples dominate.  `α` preserves
`ℓ`, hence the cone, fixes `u`, and `α² = 1`.

**Stage involutions are permutations.**  An order-automorphism of
`(Z^n, standard cone)` permutes the extreme rays of the cone and maps
each generator `e_i` to the generator of an extreme ray, i.e. is a
permutation matrix.  So an equivariant chain of simplicial groups with
involutions is a filtered system of `Z/2`-permutation modules.

**Cohomological triviality.**  A permutation module decomposes as a
direct sum of trivial modules `Z` (fixed coordinates) and regular
modules `Z[Z/2]` (2-cycles).  `H^1(Z/2, Z_triv) = Hom(Z/2, Z) = 0`,
and for `Z[Z/2]`: `ker(1 + σ) = {(a, −a)} = im(1 − σ)`, so
`H^1(Z/2, Z[Z/2]) = 0`.  Since `Z/2` is of type `FP_∞` (finite free
resolution of `Z` over `Z[Z/2]`), `H^1(Z/2, −)` commutes with
filtered colimits; hence the limit module of any equivariant
simplicial chain has `H^1 = 0`.

**The witness is not such a limit.**  For `α = diag(1,1,−1)` the
module is `Z²_triv ⊕ Z_sign`, and
`H^1(Z/2, Z_sign) = ker(1 + σ)/im(1 − σ) = Z / 2Z = Z/2 ≠ 0`.

**AF consequence.**  If `β ∈ Aut(A_G)`, `β² = id`, preserves an
increasing exhausting nest `A_1 ⊆ A_2 ⊆ ⋯` of finite-dimensional
subalgebras, then `K_0(A_G) = colim K_0(A_k)` equivariantly, and each
`K_0(β|_{A_k})` is induced by an automorphism of a finite-dimensional
C\*-algebra, which permutes the matrix-block summands (inner parts act
trivially on `K_0`) — a permutation module map.  By the previous
paragraphs no such nest exists when `K_0(β) = α`.
