---
rg: 2
id: non-ibn-rational-hosts-have-infinite-elementary-centre-proof
kind: route
title: Corner units of conjugate idempotents collapse the scalar class, and Whitehead commutators make the powers elementary
target: non-ibn-rational-hosts-have-infinite-elementary-centre
requires: []
---

**(a) Conjugate idempotents.**
- Let `e, f` be idempotents with `eL ≅ fL` and `(1-e)L ≅ (1-f)L`.
- Choose `a ∈ fLe`, `b ∈ eLf` with `ab = f` and `ba = e`. Choose `a' ∈ (1-f)L(1-e)`, `b' ∈ (1-e)L(1-f)` with `a'b' = 1-f` and `b'a' = 1-e`.
- Put `g = a + a'` and `h = b + b'`. The cross terms vanish (e.g. `ab' = ae(1-e)b' = 0`), so `gh = hg = 1`.
- Also `geh = aeb = ab = f`.

**(b) Corner units.**
- Fix a central unit `μ`. For an idempotent `e`, put `u_e = μe + (1-e)`. It is a unit with inverse `μ^{-1}e + (1-e)`.
- If `ee' = e'e = 0`, then `u_e u_{e'} = u_{e+e'}`.
- `g u_e g^{-1} = u_{geg^{-1}}`.
- So in `U^{ab}`, the class `[u_e]` depends only on the conjugacy class of `e`. It is additive over orthogonal sums, and `u_1 = μ`.

**(c) Collapse.**
- Since `L ≅ L^{1+d}`, we get `L^m ≅ L^{m+d}` for all `m >= 1`.
- Choose orthogonal idempotents `e_1, ..., e_{1+d}` with sum `1` and `e_iL ≅ L`. Each has complement `≅ L^d`, so all are conjugate by (a).
- Put `γ = [u_{e_1}]`. Then `[μ] = (1+d)γ`.
- Since `e_1L ≅ L ≅ L^{1+d}`, split `e_1 = f_1 + ... + f_{1+d}` into orthogonal idempotents with `f_iL ≅ L`.
  - The complement of `f_i` is `(e_1 - f_i)L ⊕ (1-e_1)L ≅ L^d ⊕ L^d ≅ L^d`.
  - So each `f_i` is conjugate to `e_1`, and `γ = [u_{e_1}] = Σ[u_{f_i}] = (1+d)γ`.
- Hence `dγ = 0`, so `[μ] = γ` and `d[μ] = 0`. That is, `μ^d ∈ [U,U]`.
- For `d = 1`, `γ = 0` and `μ ∈ [U,U]`.

**(d) Elementary scalars.** Let `n >= 3`.
- For a unit `x`, `diag(x, x^{-1}) = e_12(x) e_21(-x^{-1}) e_12(x) · e_12(-1) e_21(1) e_12(-1) ∈ E_2(L)`.
- For units `x, y`, the commutator of `diag(x, x^{-1}, 1, ...)` and `diag(y, 1, y^{-1}, ...)` is `diag(xyx^{-1}y^{-1}, 1, ..., 1)`. So `diag(c, 1, ..., 1) ∈ E_n(L)` for every `c ∈ [U,U]`.
- Put `λ = μ^d`, which lies in `[U,U]` by (c). Let `w_{1i} = e_{1i}(1) e_{i1}(-1) e_{1i}(1)`, a signed permutation matrix. Since `λ` is central, conjugating `diag(λ, 1, ..., 1)` by `w_{1i}` moves `λ` to position `i`.
- So `λI_n` is a product of elements of `E_n(L)`.
- `λI_n` commutes with every matrix because `λ ∈ Z(L)`. So it lies in `Z(EL_n(L))`.

**(e) Rational centre.**
- If `Q ⊆ Z(L)`, then `λ ↦ λ^d I_n` is a homomorphism `Q^× -> Z(EL_n(L))`. Its kernel is contained in `{±1}`, because `Q -> L` is injective.
- Its image contains `p^d I_n` for all primes `p`. By unique factorization these are multiplicatively independent, so they generate a free abelian group of infinite rank.
- Every subgroup of a finitely generated abelian group is finitely generated, and `Z(EL_n(L))` is abelian. So `Z(EL_n(L))` is not finitely generated.

**(f) Leavitt maps.** If `φ: L_Z(1, 1+d) -> L` is unital, the images of `x_i, y_i` satisfy `y_i x_j = δ_ij` and `Σ x_i y_i = 1`. These give mutually inverse maps `L -> L^{1+d}` (`r ↦ (y_i r)_i`) and `L^{1+d} -> L` (`(r_i) ↦ Σ x_i r_i`). ∎
