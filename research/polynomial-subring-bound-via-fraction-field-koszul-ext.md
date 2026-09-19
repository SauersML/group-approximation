---
rg: 2
id: polynomial-subring-bound-via-fraction-field-koszul-ext
kind: route
title: Resolve the fraction field of a polynomial subring by an induced Koszul complex, which stays exact because the fraction field is flat over the subring
target: quasi-free-algebras-contain-no-two-variable-polynomial-ring
requires: [quasi-free-algebras-have-no-trdeg-two-subfields]
---

All tensor products are over `k` unless marked. Modules are left modules unless marked.

## 1. Setup

Let `C = k[a_1, ..., a_n] ⊆ A'` as in the target, with `1_(A') ∈ C`. Put `K = k(y_1, ..., y_n)` and

- `R = A' ⊗ K`, a `K`-algebra;
- `S = C ⊗ K = K[a_1, ..., a_n] ⊆ R`, a commutative polynomial ring over `K`;
- `α_i = a_i ⊗ 1 - 1 ⊗ y_i ∈ S`, and `I = (α_1, ..., α_n) ⊆ S`.

The `α_i` are affine-linear in distinct variables of `S`, so they form a regular sequence, and
`S/I ≅ K` via `a_i ↦ y_i`. The Koszul complex `K_• = K_•(α_1, ..., α_n; S)` is a free `S`-resolution of `S/I` of
length `n`.

**The key identification.** Restrict `S/I` to `C` along `C -> S -> S/I`. This map sends `f(a_1, ..., a_n)` to
`f(y_1, ..., y_n)`. It is injective and its image generates the field `K`. So `S/I`, as a `C`-module, is the
fraction field `Frac(C)`. In particular it is a flat `C`-module.

## 2. A left R-module with a free resolution of length n

Regard `R` as a right `S`-module by right multiplication, and put `Q = R ⊗_S (S/I)`, a left `R`-module.

- **Base change.** As right `S`-modules, `R ≅ A' ⊗_C S` via `x ⊗ (c ⊗ μ) ↦ xc ⊗ μ`, where `A'` is a right
  `C`-module by right multiplication. `S = C ⊗ K` is free over `C`. Flat base change gives
  `Tor^S_i(A' ⊗_C S, M) ≅ Tor^C_i(A', M)` for every `S`-module `M`: resolve `A'` by flat right `C`-modules `P_•`;
  then `P_• ⊗_C S` is a flat `S`-resolution of `A' ⊗_C S`, and `(P_• ⊗_C S) ⊗_S M = P_• ⊗_C M`.
- **Vanishing.** Hence `Tor^S_i(R, S/I) ≅ Tor^C_i(A', Frac(C)) = 0` for `i >= 1`, because `Frac(C)` is flat over
  `C` (Section 1). This step needs nothing about `A'` over `C`. The subfield route needed `A'` free over the
  subring; here the flatness sits on the other side.
- **Resolution.** `H_i(R ⊗_S K_•) = Tor^S_i(R, S/I)`. So `R ⊗_S K_•` is exact in positive degrees. Each term
  `R ⊗_S S^(binom(n, i)) = R^(binom(n, i))` is a free left `R`-module, and the differentials are right
  multiplications by the `± α_i`, so they are left `R`-linear. This is a free resolution of `Q` of length `n`.

## 3. The top Ext is nonzero

Apply `Hom_R(-, R)`. We have `Hom_R(R ⊗_S K_•, R) = Hom_S(K_•, R)`, with `R` a left `S`-module by left
multiplication. This is the Koszul cochain complex of `α_1, ..., α_n` acting on `R` from the left. Its top
cohomology is

```text
Ext^n_R(Q, R) = R / (α_1 R + ... + α_n R) = (S/I) ⊗_S R.
```

As left `S`-modules, `R ≅ S ⊗_C A'`, where `A'` is a left `C`-module. So
`(S/I) ⊗_S R ≅ (S/I) ⊗_C A' = Frac(C) ⊗_C A'`. This is the localization of the `C`-module `A'` at `C ∖ 0`. The
element `1 ⊗ 1` vanishes there only if `c · 1_(A') = 0` for some nonzero `c ∈ C`. That is impossible because
`C ⊆ A'`. So `Ext^n_R(Q, R) != 0`, `pd_R Q >= n`, and `l.gl.dim(A' ⊗ K) >= n`. This proves part 1.

## 4. Consequence for quasi-free algebras

Let `pd_(A^e) A <= 1` and `r >= 1`, and suppose `φ : k[x, y] -> M_r(A)` is an injective ring homomorphism, not
necessarily unital.

- **Make it unital.** `e = φ(1)` is an idempotent and `φ(g) = e φ(g) e`. Put `ψ(f) = f(0, 0)(1 - e) + φ(f)`. This is
  a unital homomorphism. It is injective, because `e ψ(f) = φ(f)`. So `C = ψ(k[x, y])` is a polynomial subring
  with `1 ∈ C`. Two commuting algebraically independent elements give such a `φ` directly.
- **Lower bound.** Part 1 with `A' = M_r(A)` and `n = 2` gives `l.gl.dim(M_r(A) ⊗ K) >= 2`.
- **Upper bound.** `M_r(A) ⊗ K ≅ A ⊗ M_r(K)`, and `M_r(K)` is simple artinian, hence semisimple. Part 1 of
  `quasi-free-algebras-have-no-trdeg-two-subfields` gives `l.gl.dim(A ⊗ M_r(K)) <= 1`.

These contradict each other, which proves part 2. ∎

## 5. Checks

- **The bound is sharp in the right place.** `A' = k(x, y)` has `l.gl.dim A' = 0` but contains `k[x, y]`. Part 1
  gives only `l.gl.dim(k(x, y) ⊗ k(y_1, y_2)) >= 2`, which is true. No claim is made about `l.gl.dim A'`.
- **It does not over-reach.** `L ⊗ L` contains `k[s_0 ⊗ 1, 1 ⊗ s_0]`, so by part 2 it is not quasi-free. That is
  expected: Hochschild dimension of a tensor product is not bounded by the maximum of the factors. `O_2 ⊇ C(T^2)` is not a quasi-free `k`-algebra. Both are consistent with part 2, and they are the two
  examples that `research/artifacts/brownlowe-sorensen-transfer-to-f2-2026-09-13.md`, Section 5, says any proof
  must avoid.
- **Consistency with the free algebra.** `k<x, y>` is quasi-free, and Bergman's centralizer theorem gives the same
  answer: commuting pairs there generate a subring of `k[t]`.
