---
rg: 2
id: finite-multiplier-projective-models-round-strictly-proof
kind: route
title: Finite H_2 kills every pointwise-trivial class, and finite H_1 lets the scalar gauge converge to a character
target: finite-multiplier-projective-models-round-strictly
requires: []
---

Notation is as in the claim. `S` is a finite generating set of `Γ`, and
`X = Hom(Γ,T) = Hom(H_1(Γ;Z),T)`, which is finite.

## 1. The classes eventually vanish

Treat `T` as a discrete abelian group. It is divisible, hence an injective `Z`-module, so
`Ext(H_1(Γ;Z),T) = 0`. The universal coefficient theorem gives

```text
H^2(Γ;T)  ≅  Hom(H_2(Γ;Z), T),        [c] -> ( [z] -> c(z) ),
```

where `c(z) = Π c(g,h)^(a_(g,h))` for a bar 2-cycle `z = Σ a_(g,h) [g|h]`.

Let `e` be the exponent of `H_2(Γ;Z)`, and choose bar 2-cycles `z_1..z_m` whose classes
generate `H_2(Γ;Z)`.
- Each `c_n(z_j)` is a finite product of values of `c_n`, so `c_n(z_j) -> 1`.
- Since `e[z_j] = 0`, `c_n(z_j) ∈ μ_e`.
- Hence there is `n_0` with `c_n(z_j) = 1` for all `j` and all `n >= n_0`, i.e. `[c_n] = 0`.

For `n >= n_0` choose `b_n : Γ -> T` with

```text
c_n(g,h) = b_n(g) b_n(h) b_n(gh)^(-1).
```

## 2. A genuine representation after a gauge change

Put `π'_n(g) = b_n(g)^(-1) α_n(g)`. Then

```text
π'_n(g) π'_n(h) = b_n(g)^(-1) b_n(h)^(-1) c_n(g,h) α_n(gh) = b_n(gh)^(-1) α_n(gh) = π'_n(gh),
```

so `π'_n` is a homomorphism into `U(d_n)`. The gauge `b_n` is unique up to multiplication by
an element of `X`.

## 3. The gauge converges to a character

Let `ε_n = min_(χ∈X) max_(s∈S) |b_n(s) χ(s)^(-1) - 1|`. Suppose `ε_n` does not tend to 0.
- Then there are `ε > 0`, a subsequence with `ε_n >= ε`, and a nonprincipal ultrafilter `ω` on
  it.
- By compactness of `T`, `b_ω(g) = lim_ω b_n(g)` exists for every `g`.
- `b_ω(g) b_ω(h) b_ω(gh)^(-1) = lim_ω c_n(g,h) = 1`, so `b_ω ∈ X`.
- Then `lim_ω max_(s∈S) |b_n(s) b_ω(s)^(-1) - 1| = 0`, which contradicts `ε_n >= ε`.

So `ε_n -> 0`. Choose minimizers `χ_n ∈ X` and put `β_n = b_n χ_n^(-1)`.
- `max_(s∈S) |β_n(s) - 1| -> 0`.
- `χ_n` is multiplicative, so `β_n(g) β_n(h) β_n(gh)^(-1) = c_n(g,h) -> 1`.
- Induction on word length, using `β_n(gs) = β_n(g) β_n(s) c_n(g,s)^(-1)` and
  `β_n(s^(-1)) = c_n(s,s^(-1)) β_n(e) β_n(s)^(-1)`, gives `β_n(g) -> 1` for every `g`. Here
  `β_n(e) = c_n(e,e) -> 1`.

## 4. Conclusion

Put `π_n = χ_n π'_n`, a genuine representation on `C^(d_n)`. Then
`α_n(g) = b_n(g) π'_n(g) = β_n(g) π_n(g)`, so `||α_n(g) - π_n(g)||_op = |β_n(g) - 1| -> 0`
for every `g`.

The corollaries in the claim body follow from the universal coefficient theorem, with
`Hom(finite, torsion-free) = 0` and `Ext(0, A) = 0`.
