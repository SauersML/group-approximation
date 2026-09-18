---
rg: 2
id: divisor-level-subpairs-rank-three-twisted-cone-proof
kind: route
title: Compute the trace of a graded twist subgroup on Gamma, then reduce it modulo a height-one prime or a square ideal
target: divisor-level-subpairs-cannot-certify-rank-three-twisted-cone
requires:
  - block-subpairs-make-twisted-kazhdan-cones-nonsofic
  - kt-pair-group-double-is-nonsofic
---

Notation is as in [[divisor-level-subpairs-cannot-certify-rank-three-twisted-cone]].  Facts used:

- (S) Suslin: `SL_n(k[x_1..x_d]) = EL_n` and `SL_n(k[x_1^(±1)..x_d^(±1)]) = EL_n` for a field `k` and `n ≥ 3`.
- (W) Whitehead: a diagonal matrix with unit entries and determinant 1 lies in `EL_n`.
- (T1) `EL_3(A)` is Kazhdan for every finitely generated commutative ring `A` (Ershov-Jaikin-Kassabov).
  `Z^k x| SL_k(Z)` is Kazhdan for `k ≥ 3`.  An extension of a Kazhdan group by a Kazhdan group is Kazhdan.
  A quotient of a Kazhdan group is Kazhdan, and an infinite amenable group is not Kazhdan.

For `m ∈ Z^d`, `x^m` is a Laurent monomial and `supp f ⊆ Z^d` is the set of exponents of `f`.

## (D1)

*`B ≤ G`.*  `D` is diagonal with unit entries and `det D = x^(a_1+a_2+a_3) = 1`, so `D ∈ EL_3(R)` by (W).  Hence
`B` is a conjugate in `G` of a subgroup of `G`.

*The trace.*  For `e ∈ EL_3(F_q[L])` and `σ ∈ H`, `D e σ D^-1 = (D e σ(D)^-1) σ`, and this lies in `EL_3(R)` only
when `σ = 1`.  So `B ∩ EL_3(R) = D EL_3(F_q[L]) D^-1 = D SL_3(F_q[L]) D^-1` by (S), since `F_q[L]` is a
Laurent ring in `d` variables.  The `(i,j)` entry of `D e D^-1` is `x^(a_i - a_j) e_ij`.  Hence

```text
B ∩ EL_3(R) = { g ∈ SL_3(R) : supp g_ij ⊆ a_i - a_j + L  for all i, j } ,
```

and `C = B ∩ Gamma` is the set of such `g` with entries in `R_+`, because `Gamma = SL_3(R_+)` by (S).

*Origin image.*  For `i ≠ j`, `0 ∉ a_i - a_j + L`, so `g_ij` has no constant term and `ev_0(g)` is diagonal.
The image `Tbar` of the diagonal torus of `SL_3(F_q)` in `F` is abelian.  For `q = 2` it is trivial, so
`psi(C) = 1` and every `h ≠ 1` centralises it.  For `q ≥ 3` it has order `(q-1)^2 / gcd(3, q-1) > 1`, and every
`h ∈ Tbar \ 1` centralises `psi(C)`.

*The special case.*  Now `L = nZ ⊕ Z^(d-1)` with `n ≥ 3`, `a_i = α_i e_1`, and
`H = { σ ∈ Stab(L) : σ e_1 = e_1 }`.  In coordinates `m = (m_1, u)`, `u ∈ Z^(d-1)`, an element of `H` acts by
`σ(m_1, u) = (m_1 + w·u, M u)` with `w ∈ nZ^(d-1)` and `M ∈ SL_(d-1)(Z)`.  So `H ≅ Z^(d-1) x| SL_(d-1)(Z)`.

- *(T).*  `EL_3(F_q[L])` and `H` are Kazhdan for `d ≥ 4` by (T1), hence so is `B`.
- *Compressors.*  Let `σ ∈ H` have nonnegative entries, meaning `w ≥ 0` and `M ≥ 0`.  Then `σ(D) = D`, so
  `D σ D^-1 = σ ∈ B`.  For `g ∈ C`, `σ g σ^-1 = σ(g)` has `supp σ(g)_ij = σ(supp g_ij)`.  This lies in
  `N^d`, since `σ ≥ 0`, and in `a_i - a_j + L`, since `σ` fixes `a_i - a_j` and preserves `L`.  So `σ` compresses
  `C`.  These `σ` generate `H`: the matrices with `M = I`, `w = n e_k`, and those with `w = 0`, `M = I + E_kl`, are
  nonnegative.
- *Generation.*  Fix `i ≠ j`, `v = a_i - a_j` and `m = (m_1, u) ∈ L`.  If `u ≠ 0`, let `c = gcd(u)` and pick `M`
  with `M (c e_1) = u`.  For `K ≫ 0` put `m' = (m_1 + nKc, c e_1) ∈ L` and `τ = (w = -nK e_1, M) ∈ H`.  Then
  `τ m' = m`, `v + m' ≥ 0`, so `e_ij(x^(v+m')) ∈ C` and `τ e_ij(x^(v+m')) τ^-1 = e_ij(x^(v+m))`.  If `u = 0`, pick
  `k ∉ {i, j}` and `u_0 ≠ 0`, and write `e_ij(x^(v+m)) = [e_ik(x^(a_i - a_k + (m_1, u_0))), e_kj(x^(a_k - a_j + (0, -u_0)))]`,
  a commutator of two elements of the first kind.  So `<C, H>` contains `D EL_3(F_q[L]) D^-1` and `H`, hence
  equals `B`.  The compressors generate `B`: `C` is infranormal in `B`.
- *Not normal.*  Choose `k` with `v = a_i - a_j` having `v_1 + k ∈ [0, n)` and `k ≡ 0 mod n`, and
  `g = e_ij(x^(v + (k, e_1))) ∈ C`.  For `τ = (w = -n e_1, I)`, `τ g τ^-1 = e_ij(x^(v + (k - n, e_1)))` has
  negative first exponent, so it is not in `C`.

## (D2)

Relabel so that the residues `α_1 < α_2 < α_3` lie in `[0, n)`.  Write `t = x_1`, `y = (x_2..x_d)`, `u = t^n` and
`S = F_q[u, y] = F_q[L ∩ N^d]`.  Let `c_ij ∈ [0, n)` be the residue of `α_i - α_j`.  Then
`{ f ∈ R_+ : supp f ⊆ a_i - a_j + L } = t^(c_ij) S`, and

```text
Lambda = ⊕ t^(c_ij) S E_ij   is a subring of M_3(R_+),  and  C = Lambda ∩ SL_3(R_+) .
```

Here `c_ij = α_i - α_j` for `i ≥ j` and `c_ij = n + α_i - α_j` for `i < j`.  In both cases
`c_ik + c_kj = c_ij` when `j ≤ k ≤ i`, and `c_ik + c_kj = c_ij + n` when `i ≥ j` and `k ∉ [j, i]`.

Define `π : Lambda -> M_3(F_q[y])` by `π(λ)_ij = (t^(-c_ij) λ_ij) mod u` for `i ≥ j`, and `π(λ)_ij = 0` for
`i < j`.  The image is lower triangular.  `π` is additive and unital.  It is multiplicative: for `i ≥ j`,
`(λ μ)_ij = Σ_k λ_ik μ_kj`, and the term `k` lies in `t^(c_ik + c_kj) S`.  For `k ∉ [j, i]` this is
`t^(c_ij) u S`, which `π` kills.  For `k ∈ [j, i]` it is `t^(c_ij)` times the product of the two reduced entries.
So `π` restricts to a homomorphism from `C` to the invertible lower-triangular matrices over `F_q[y]`, a
solvable group.

The image is infinite: for `f ∈ F_q[y]`, `e_21(t^(c_21) f) ∈ C` and `π` sends it to `e_21(f)`.  With `d ≥ 2`,
`F_q[y]` is infinite.  So `C` has an infinite amenable quotient and is not Kazhdan by (T1).

## (D3)

`I_+ = I ∩ R_+` is nonzero, since every element of `I` has a monomial multiple in `R_+`, and proper.

*`R/I` infinite.*  `R/I` is the localisation of `R_+/I_+` at the images of the `x_i`, so `R_+/I_+` is infinite.
Some minimal prime `P ⊇ I_+` then has `R_+/P` infinite.  `(I_+)_P` is a nonzero ideal in the radical of the local
ring `(R_+)_P`, so `(I_+/I_+^2)_P ≠ 0` by Nakayama.  A prime filtration of the finitely generated module
`I_+/I_+^2` then has a factor `R_+/Q` with `Q ⊆ P`, which is infinite.  So `I_+/I_+^2` is infinite.

`C ⊆ SL_3(R, I) ∩ SL_3(R_+) = SL_3(R_+, I_+)`.  The map `φ(g) = (g - 1) mod I_+^2 ∈ M_3(I_+/I_+^2)` is a
homomorphism to an abelian group on `SL_3(R_+, I_+)`, since `(1 + a)(1 + b) = 1 + a + b + ab` with
`ab ∈ M_3(I_+^2)`.  `C` contains `EL_3(R, I) ∩ Gamma ∋ e_12(f)` for `f ∈ I_+`, and `φ(e_12(f)) = f E_12`.
So `φ(C)` is an infinite abelian group, and `C` is not Kazhdan.

*`R/I` finite.*  `V(I)` is a finite set of points of the torus, and `V(I_+)` is its closure in affine space,
the same finite set.  It misses the origin, so `I_+ + m_0 = R_+`.  Pick `f ∈ I_+` with `f(0) = 1`.  Then
`e_ij(f) ∈ C` and `ev_0(e_ij(f)) = e_ij(1)`, so `psi(C) = F`, which is centreless.  Condition (i) fails.

If `I_+ ⊆ m_0`, the second case is impossible, so the first applies.

## (D4)

In (D2) the level is imposed modulo the height-one prime `(t)`, after the change of lattice `t ↦ u = t^n`,
and the quotient `π` lands in a Borel subgroup over `R_+/(t) = F_q[y]`.  In (D3) it is imposed modulo `I_+`,
and survives in `I_+/I_+^2`.  Both quotients are infinite because the level set is positive-dimensional.

## (D5)

For `i ≠ j` let `E_ij = { m ∈ Z^d : e_ij(x^m) ∈ B }`, and let `S = H_B · { m ∈ N^d : |m| ≥ k }`.

- `S ⊆ E_ij`: for `σ ∈ H_B`, `σ e_ij(x^m) σ^-1 = e_ij(x^(σ m))`.
- `E_ik + E_kj ⊆ E_ij` for distinct `i, j, k`: `[e_ik(x^m), e_kj(x^m')] = e_ij(x^(m + m'))`.

By induction on `n ≥ 2`, every sum of `n` elements of `S` lies in every `E_ij`.  The case `n = 2` is the second
bullet applied to the first.  For `n + 1`, write the sum as (sum of `n`) + (one), which lies in `E_ik + E_kj`.

Let `P` be the additive semigroup generated by `S`.  Its cone equals the cone spanned by `H_B · R_+^d`, since
removing a bounded set from `N^d` does not change its cone.  Suppose that cone is `R^d`, and take `v ∈ S`.
Then `-v` is a nonnegative rational combination of elements of `S`, so `-Nv ∈ P` for some `N ≥ 1`.  Hence
`0 = Nv + (-Nv)` is a sum of at least two elements of `S`, and `0 ∈ E_ij`.  So `e_ij(1) ∈ B ∩ Gamma = C` for
all `i ≠ j`, and `psi(C)` contains the image of `EL_3(F_q) = SL_3(F_q)`, which is `F`.

If the cone `K` spanned by `H_B · R_+^d` is not `R^d`, its closure `Kbar` is a proper closed convex cone
containing `R_+^d`.  So `Kbar` has nonempty interior, and its dual `K*` is nonzero, pointed, contained in the
dual orthant and `H_B`-invariant under the transpose action.

*Example.*  In the basis `E_ii`, `P_ij = (e_i + e_j)(e_i + e_j)^T` of `Sym^2 Z^3` (a lattice basis, since
`E_ij + E_ji = P_ij - E_ii - E_jj`), `g ↦ (X ↦ g X g^T)` preserves the PSD cone.  That cone contains the orthant,
so `H` preserves a proper cone, and (D5) does not exclude `B = <Gamma(m_0), H>`.  A nonnegative
matrix `σ ∈ H` maps the orthant into itself and preserves the PSD cone, so it maps the extreme rays of the PSD
cone lying in the orthant to such rays.  A rank-one `v v^T` has coordinates `v_i v_j` on `P_ij` and
`v_i^2 - v_i Σ_(j≠i) v_j` on `E_ii`.  For `v ≥ 0` these are all nonnegative only when `v` has one nonzero entry,
or two equal ones.  So those rays are exactly the six basis rays, `σ` permutes the basis, and the nonnegative
elements of `H` form a finite group.
