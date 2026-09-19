---
rg: 2
id: leavitt-polynomial-pairs-singular-element-proof
kind: route
title: Invert all of k[a, b] universally; the localization stays quasi-free and would contain k(a, b), so it is zero, and compactness gives one singular element
target: leavitt-polynomial-pairs-contain-a-universally-singular-element
requires: [universal-localizations-of-quasi-free-algebras-are-quasi-free, quasi-free-algebras-have-no-trdeg-two-subfields, leavitt-algebra-hochschild-dimension-at-most-one, leavitt-algebras-l-k-1-n-are-simple]
---

Let `A`, `C`, `Σ = C ∖ 0` be as in the claim, and `B = A_Σ`.

1. **B is quasi-free.** `B` is the universal localization at the right multiplications `c : A -> A`, `c ∈ Σ`.
   By `universal-localizations-of-quasi-free-algebras-are-quasi-free`, `pd_(B^e) B <= 1`. `k` stays central in `B`.
   For `A = L_k(1,2)` the hypothesis is `leavitt-algebra-hochschild-dimension-at-most-one`.
2. **If B ≠ 0 it contains Frac(C).** The kernel of `A -> B` is a two-sided ideal missing `1`. `A` is simple
   (`leavitt-algebras-l-k-1-n-are-simple` for Leavitt algebras), so `A -> B` and `C -> B` are injective. The images
   of `Σ` are units that commute, so their inverses commute with each other and with `C`. Hence
   `p/q ↦ p q^(-1)` is a well-defined homomorphism `Frac(C) -> B`, injective because `Frac(C)` is a field.
3. **So B = 0.** Otherwise step 2 gives a subfield of `B` containing `k · 1` of transcendence degree `>= 2`
   (pick two algebraically independent elements of `Frac(C)` and restrict to the subfield they generate). This
   contradicts item 3 of `quasi-free-algebras-have-no-trdeg-two-subfields` with `r = 1`, applied to `B`.
4. **One element suffices.** `A_Σ` is the directed colimit of `A_(Σ_0)` over finite `Σ_0 ⊆ Σ` (it is presented by
   adjoining inverses; each relation uses finitely many). A directed colimit of rings with `1 = 0` has `1 = 0` at
   some stage, so `A_(p_1, ..., p_m) = 0` for some `p_i ∈ Σ`. Put `p = p_1 ⋯ p_m`. In `A_p`, `p^(-1)` commutes
   with each `p_j`, so `p_i · (∏_(j ≠ i) p_j) p^(-1) = 1 = (∏_(j ≠ i) p_j) p^(-1) · p_i`. So `A_(p_1..p_m) -> A_p`
   exists and `A_p = 0`. For `q ∈ Σ`, inverting `pq` inverts `p` the same way, so `A_(pq) = 0`.
5. **The two examples in the claim.** Write `S = s_0` on `F(X, k)`, `(Sf)(ω) = [ω_0 = 0] f(σω)`, and let `m(ω)`
   be the number of leading zeros.
   - `(1 + S) f = g` reads `f(ω) = g(ω) - [m(ω) >= 1] f(σω)` for `ω ≠ 0^∞`, with `m(σω) = m(ω) - 1`, and
     `2 f(0^∞) = g(0^∞)`. Induction on `m` gives a unique solution when `char k ≠ 2`.
   - `(1 + S + S^2) f = g` reads `f(ω) = g(ω) - [m >= 1] f(σω) - [m >= 2] f(σ^2 ω)` and `3 f(0^∞) = g(0^∞)`.
     Unique solution when `char k ≠ 3`.
   - With `g = 1` the solutions depend only on `m(ω)`: `1, 0, 1, 0, ...` and `1, 0, 0, 1, 0, 0, ...`. Every
     neighbourhood `0^n X` of `0^∞` contains points of every `m >= n`, so neither solution is locally constant.
     `LC(X, k)` is an `L`-submodule, and a unit of `L` would be bijective on it with inverse the restriction of
     the `F(X, k)` inverse. So neither element is a unit, yet each is bijective on the nonzero module `F(X, k)`. ∎

**Where the method stops.** Step 4 is sharp: the argument gives no information about *which* element is singular.
`C = k[s_0]` (trdeg 1) already contains the singular element `s_0`, so singular elements alone do not bound
the transcendence degree. What is left of Q_2 is a statement about centralizers of universally singular elements.
