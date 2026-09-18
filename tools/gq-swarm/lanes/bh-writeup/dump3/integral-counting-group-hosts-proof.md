---
rg: 2
id: integral-counting-group-hosts-proof
kind: route
title: Congruence kernels, scalar commutators and injective reduction mod p exclude Leavitt-linear simple hosts of Γ_Z
target: integral-counting-group-avoids-leavitt-linear-simple-hosts
requires:
  - leavitt-tensor-unit-word-problems-have-one-counting-quantifier
  - leavitt-scalar-commutators-block-fp-central-quotients
---

Lane proof (bh-free-26), elementary. Notation as in `leavitt-tensor-unit-counting-cap-proof`.

## 0. Integral forms

Let `A_Z` be the `Z`-span of the monomials `⊗_j s_(α'_j) t_(α_j)` in `A_Q`. It is a subring,
because products of monomials are `0` or monomials. It is a free `Z`-module on the
normal-form monomials: Leavitt path algebras over a commutative ring have the reduced-path
basis, and tensor products of free modules are free. So `A_(Z[1/M]) = A_Z ⊗ Z[1/M]`, and for
`p ∤ M`, reduction of coefficients `π_p : A_(Z[1/M]) → A_(F_p)` is a surjective ring map. A
coefficient in `Z[1/M]` divisible by every prime `p ∤ M` is `0`.

## 1. Congruence kernels (part 1)

In `Γ_Z`, `T(c,1,d) = [T(c,1,e), T(e,1,d)] = 1 + a_c a_d^*`, by (★_p) with `L = R' = 1`. Then
`T(c,1,d)^m = 1 + m a_c a_d^*`, because `(a_c a_d^*)^2 = 0`. So `T(c,1,d)^p` is a nontrivial
element of `ker π_p ∩ Γ_Z`, and `T(c,1,d) ∉ ker π_p`. For any `G ⊇ Γ_Z`, `ker(π_p|_G)` is a
normal subgroup, nontrivial and proper. This gives (i).

For (ii), put `D = [U_M, U_M]` and `K = ker π_p ∩ D`. Then:
- `x = T(c,1,d)^p ∈ K` is a power of a commutator of transvections.
- `y = T(d,1,c) = [T(d,1,e), T(e,1,c)] ∈ D` does not commute with `x`:
  `(a_c a_d^*)(a_d a_c^*) = a_c a_c^* ≠ a_d a_d^* = (a_d a_c^*)(a_c a_d^*)`.
- So `x ∉ Z(D)`, and `KC/C ≠ 1` for every central `C`.
- If `KC = D`, then `π_p(D) = π_p(C)` would be abelian. But `π_p(T(c,1,d))` and `π_p(T(d,1,c))`
  do not commute in `A_(F_p)`, by the same computation. So `KC/C` is proper.

The same argument works for `U_M` in place of `D`.

## 2. Scalars (part 2)

This is `leavitt-scalar-commutators-block-fp-central-quotients`, part 1, with `K = Q` and
`d = 2`. There `C_0 = Q^x`.

## 3. Injective reduction (part 3)

Let `G ≤ GL_N(A_Q)` be finitely generated and simple, with `G ≠ 1`. The finitely many
coefficients of the generators and their inverses lie in some `Z[1/M]`, so
`G ≤ GL_N(A_(Z[1/M]))`. For `p ∤ M`, `ker(π_p|_G)` is normal, so it is `1` or `G`.

If it were `G` for every `p ∤ M`, then every `g ∈ G` would have all coefficients of `g - 1`
divisible by every such `p`, hence `g = 1`, and `G = 1`. So `π_p` is injective on `G` for some
`p`.

- (a) Let `g = 1 + X ∈ G` with `X^2 = 0` and `X ≠ 0`. Then `g^p = 1 + pX ≠ 1` in characteristic
  `0`, while `π_p(g)^p = 1 + p π_p(X) = 1`. This contradicts injectivity. So no such `g`
  exists. `T(c,1,e) = 1 + a_c a_e^* ∈ Γ_Z` is of this form.
- (b) `WP(G) = WP(π_p(G))` for corresponding generators, and it lies in `∀·Mod_pP` by
  `leavitt-tensor-unit-word-problems-have-one-counting-quantifier`, part 1. An embedding
  `ι : Γ_Z → G` reduces `WP(Γ_Z)` to `WP(G)` by substituting fixed words for the letters.
  `WP(Γ_Z)` is `C_=P`-complete, so `C_=P ⊆ ∀·Mod_pP`.

## 4. Finite fields (part 4)

The same substitution argument applies, with part 1 of the ceiling node.

## 5. Affine actors (part 5)

Let `M_Z = C(C^k, Z[1/M])`, and let `G ≤ (A_(Z[1/M]))^x` act `Z[1/M]`-linearly. For
`f ∈ M_Z` and a prime `p ∤ M`, let `v_p(f)` be the least `p`-adic valuation of a value of `f`,
with `v_p(0) = ∞`. For `u ∈ G`:
- `u` and `u^(-1)` map `p^j M_Z` into itself, so `v_p(uf) = v_p(f)`.
- In the affine group `M_Z ⋊ G`, the pair `(f, f')` goes to `(uf + m, uf' + m)`, and
  `v_p(f' - f)` is preserved.

It takes every value `0, 1, 2, ...`, for instance on the pairs `(0, p^j 1)`. So there are
infinitely many orbits on pairs, and the action is not oligomorphic. The same holds on any
subset of `M_Z` containing the pairs `(0, p^j 1)` for infinitely many `j`, in particular on
`M_Z` itself, which is a single orbit of the translations.

## 6. The oracle remark

The remark is standard. Relative to an oracle `A`, the language
`{1^n : |A ∩ {0,1}^n| = 2^(n-1)}` lies in `C_=P^A`. A `(∀·Mod_pP)^A` machine for it would give,
on `N = 2^n` oracle bits, a circuit of size `2^(poly(n))` of the form AND of MOD_p of
polylog-width DNFs, which is quasi-polynomial `AC^0[p]`. Padding with constants reduces
Majority to OR of polynomially many exact-half tests. Razborov--Smolensky forbids
quasi-polynomial `AC^0[p]` circuits for Majority. The usual diagonalization gives the oracle.
