---
rg: 2
id: strict-pair-linear-shadows-over-z-proof
kind: route
title: Slide the second site of two-site monomials along an infinite cyclic direction, and read strictness through Stone duality
target: strict-pair-linear-shadows-exist-over-z
requires:
  - finite-pattern-orbit-closure-forces-surjunctivity
---

Complete proof. Notation is as in the target.

The only imported fact is the existence of a local decoder for an injective automaton. It is proved in full in
`finite-pattern-projective-decoder-proof`, section "Every injective full-shift automaton has a local decoder", the
route of the required claim. We use it only in (B1).

## Step 0. The tensor basis and dependence sets

Fix a basis `ψ_0 = 1, ψ_1, ..., ψ_{k-1}` of the functions `A -> K`, with `ψ_i = δ_{a_i} - 1/k` for `i >= 1` when
`char K` does not divide `k`, and any basis extending `1` otherwise. For `K = R` or `C`, take instead an
orthonormal basis of `L^2(A, uniform)` with `ψ_0 = 1`.

For a finite `F ⊆ G` and `c : F -> {1, ..., k-1}`, put `m_{F,c}(x) = Π_{v ∈ F} ψ_{c(v)}(x(v))`, with `m_{∅} = 1`.

**(0a) The `m_{F,c}` form a basis of `O`.** The functions on `A^E` for finite `E` are `⊗_{v ∈ E} K^A`, with the
tensor basis `{m_{F,c} : F ⊆ E}`. Enlarging `E` tensors with `1`, so it preserves the basis.

**(0b) `D(f)` is the union of the supports of the basis monomials in `f`.** Fix `v`, and write
`O = K^A ⊗ O_{≠v}`, where `O_{≠v}` is the functions not depending on `x(v)`. Then `f = Σ_i ψ_i(x(v)) f_i`, with
unique `f_i` in `O_{≠v}`. Now `f` does not depend on `x(v)` iff `f_i = 0` for all `i >= 1`, and this holds iff no
basis monomial of `f` has `v` in its support.

**(0c) The action on the basis.** With the left shift `(gx)(v) = x(g^{-1} v)` and `(g.f)(x) = f(g^{-1} x)`, we have
`g.m_{F,c} = m_{gF, c(g^{-1} ·)}`. So `G` permutes the basis, translating supports on the left.

**(0d) The trace.** If `∫ ψ_i = 0` for `i >= 1`, then `∫ m_{F,c} dμ = 0` for `F != ∅`. So `∫ f dμ` is the
coefficient of `1` in `f`. This holds for both choices of basis in characteristic 0.

## Step 1. The sliding family

Let `t` have infinite order. For `g ∈ G` and `n >= 1`, put

    e_{g,n} = ψ_1(x(g)) ψ_1(x(g t^n)) = m_{{g, g t^n}, 1}.

**(1a) `(g, n) -> e_{g,n}` is injective.** Suppose `{g, g t^n} = {h, h t^m}` with `n, m >= 1`. Either `g = h` and then
`t^n = t^m`, so `n = m`. Or `g = h t^m` and `h = g t^n`, and then `t^{n+m} = 1`, which is impossible.

Let `E = {e_{g,n}}`. By (0c), `h.e_{g,n} = e_{hg,n}`, so `E` and its complement in the basis are `G`-invariant.

**(1b) Definition.** Put `L e_{g,n} = e_{g,n+1}`. Put `R e_{g,n} = e_{g,n-1}` for `n >= 2` and `R e_{g,1} = 0`. Let
`L` and `R` fix every basis monomial outside `E`, and extend both linearly.

## Step 2. Verification of (A)

1. **One-sided inverses.** On the basis, `R L = id`. Also `L R e_{g,1} = 0 != e_{g,1}`. `L` is injective on the
   basis, and its image misses `e_{g,1}`.
2. **Unital, trivial in low degree.** Monomials of degree 0 and 1 lie outside `E`, so they are fixed.
3. **Finite propagation.** `D(L e_{g,n}) = {g, g t^{n+1}} ⊆ {g, g t^n}{1, t}`. `L` maps distinct basis monomials to
   distinct basis monomials, so there is no cancellation. So by (0b), `D(Lf)` is the union of the supports of the
   `L`-images of the monomials of `f`, and this lies in `D(f){1,t}`. For `R`, cancellation can only shrink
   supports, and `D(R e_{g,n}) ⊆ {g, g t^n}{1, t^{-1}}`.
4. **`K[G]`-linearity.** `L(h.e_{g,n}) = e_{hg,n+1} = h.L(e_{g,n})`, and similarly for `R`. On monomials outside `E`,
   both maps are the identity.
5. **Degree, monomiality and trace.** Degree 2 is kept on `E`. The basis is sent to basis or `0`. `1` is fixed, and
   no nonconstant monomial is sent to a multiple of `1`. So by (0d) the integral is preserved.
6. **`L^2`.** With the orthonormal choice, the `m_{F,c}` are an orthonormal basis of `L^2(A^G, μ)`, because
   product measure makes monomials with distinct `(F,c)` orthogonal. `L` sends this basis injectively into
   itself, so it extends to an isometry. It is not unitary, since `e_{g,1}` is orthogonal to its range.
   - Check that `⟨L b, b'⟩ = ⟨b, R b'⟩` on basis vectors. If `b' = L b`, then `R b' = b` and both sides are `1`.
     If `b' = L b''` with `b'' != b`, then `R b' = b''` and both sides are `0`. If `b'` is not in `L`(basis), then
     `b' = e_{g,1}` for some `g`, `R b' = 0`, and both sides are `0`. So `L^* = R`.
   - `G` acts unitarily by permuting the basis, and `L` commutes with it.

## Step 3. Verification of (B)

Let `X = A^G`.

**(B1).**
- Suppose `T S = id`. Then `T` is surjective. If `τx = τy`, every `Tf = f ∘ τ` agrees at `x` and `y`. So every
  element of `O` agrees there, and `x = y`, since the one-site indicators separate points.
- Conversely, let `τ` be injective, and let `σ` be a local decoder (the imported section). Then
  `T σ^* f = f ∘ σ ∘ τ = f`. `σ^*` has finite propagation with `U = ` memory of `σ`, and it is `K[G]`-linear
  because `σ` commutes with the shift.

**(B2).**
- If `τ` is surjective and `f ∘ τ = 0`, then `f = 0`.
- If `τ` is not surjective, then `τ(X)` is closed and proper. Some cylinder `[p]` with finite window is disjoint
  from it, and its indicator `1_{[p]}` is a nonzero element of `O` with `T 1_{[p]} = 0`.
- If `S T = id`, then `T` is injective. So for injective `τ`, `S T != id` for every right inverse iff `τ` is not
  surjective.

**(B3).** Let `φ` be a unital `G`-equivariant algebra endomorphism of `O`.
- Idempotents of `O` are the indicators of clopen sets. `φ` preserves products, `1` and `1 - e`, so it restricts
  to a Boolean-algebra endomorphism of `Clopen(X)`.
- By Stone duality there is a unique continuous `h : X -> X` with `φ(1_C) = 1_{h^{-1} C}`. Indicators span `O`, so
  `φ f = f ∘ h`.
- Equivariance gives `f ∘ h ∘ g^{-1} = f ∘ g^{-1} ∘ h` for all `f` in `O`, and `O` separates points, so `h` commutes
  with the shift. By Curtis–Hedlund–Lyndon, which holds over every group, `h` is a cellular automaton.
- Conversely, every pullback is such an endomorphism.
- With (B1) and (B2), `G` has a strict automaton on `A^G` iff this monoid contains a surjective, non-injective
  element.

## Step 4. Why the class dies at the stated step

- **The module structure.** By (0a) and (0c), `O = K1 ⊕ ⊕_{orbits} K[G/H]`, where `H` is the stabilizer of a
  nonempty finite support, which is finite (as in `finite-pattern-projective-decoder-proof`). Step 1 exhibits a
  countable family of free orbits, indexed by `n >= 1`, on which `L` is the unilateral shift. Such a shift exists on
  any infinite direct sum of copies of one projective, and Step 2.3 shows it can have finite propagation.
- **What a linear argument can reach.** It can use only the listed properties. Stable finiteness of `K[G]` (all
  groups in characteristic 0) or von Neumann dimension controls one-sided inverses only on finitely generated, or
  finite-dimension, pieces.
- **Where the extension needs multiplicativity.** On the one-site piece `W`, both `(L, R)` and `(T, S)` satisfy
  `S T = id`. The extension to `O` holds for `(T, S)` because `O` is generated by `W` as an algebra and `S T` is an
  algebra map. It fails for `(L, R)`, where `L R e_{g,1} = 0`.
- **Conclusion.** So any valid argument must use that `S T` (or `T`) is multiplicative at a step that is not purely
  module-theoretic.
