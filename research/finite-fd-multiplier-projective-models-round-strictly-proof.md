---
rg: 2
id: finite-fd-multiplier-projective-models-round-strictly-proof
kind: route
title: Finiteness of the realized classes kills pointwise-trivial classes, and compactness lets the scalar gauge converge to a character
target: finite-fd-multiplier-projective-models-round-strictly
requires: []
---

Notation is as in the claim. `S` is a finite generating set of `Γ`, and
`X = Hom(Γ;T)`, a closed subgroup of `T^S` (a character is determined by its values on `S`),
hence compact.

## 1. The classes eventually vanish

Treat `T` as a discrete abelian group. It is divisible, hence an injective `Z`-module, so
`Ext(H_1(Γ;Z),T) = 0`. The universal coefficient theorem gives

```text
H^2(Γ;T)  ≅  Hom(H_2(Γ;Z), T),        [c] -> ( [z] -> c(z) ),
```

where `c(z) = Π c(g,h)^(a_(g,h))` for a bar 2-cycle `z = Σ a_(g,h) [g|h]`. Coboundaries
evaluate to `1` on cycles, so this pairing is well defined on classes.

Choose bar 2-cycles `z_1..z_m` whose classes generate `H_2(Γ;Z)`. A homomorphism
`H_2(Γ;Z) -> T` is determined by its values on generators, so

```text
ev : H^2(Γ;T) -> T^m,     [c] -> ( c(z_1), ..., c(z_m) )
```

is injective.
- Each `c_n(z_j)` is a finite product of values of `c_n`, so `ev([c_n]) -> (1,...,1)`.
- `[c_n] ∈ R` because `c_n` is the exact cocycle of the finite-dimensional projective
  representation `α_n`.
- `ev(R)` is a finite subset of `T^m` containing `ev(0) = (1,...,1)`. Choose a neighbourhood
  `U` of `(1,...,1)` with `U ∩ ev(R) = {(1,...,1)}`.
- For large `n`, `ev([c_n]) ∈ U ∩ ev(R)`, so `ev([c_n]) = ev(0)` and `[c_n] = 0` by
  injectivity.

For those `n` choose `b_n : Γ -> T` with `c_n(g,h) = b_n(g) b_n(h) b_n(gh)^(-1)`.

## 2. A genuine representation after a gauge change

Put `π'_n(g) = b_n(g)^(-1) α_n(g)`. Then

```text
π'_n(g) π'_n(h) = b_n(g)^(-1) b_n(h)^(-1) c_n(g,h) α_n(gh) = b_n(gh)^(-1) α_n(gh) = π'_n(gh),
```

so `π'_n` is a homomorphism into `U(d_n)`. The gauge `b_n` is unique up to multiplication by
an element of `X`.

## 3. The gauge converges to a character

Let `ε_n = min_(χ∈X) max_(s∈S) |b_n(s) χ(s)^(-1) - 1|`. The minimum exists because `X` is
compact and the expression is continuous in `χ ∈ X ⊂ T^S`. Suppose `ε_n` does not tend to 0.
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

This is the argument of `finite-multiplier-projective-models-round-strictly-proof`, with its
Step 1 replaced by the finiteness of `R` and its Step 3 run over the compact group `X`, which
need not be finite.
