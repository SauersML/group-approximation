---
rg: 2
id: leavitt-polynomial-pairs-contain-a-universally-singular-element
kind: claim
title: A polynomial subring k[a, b] of L_k(1,2) must contain one element that acts non-bijectively on every nonzero L-module, equivalently whose universal localization is zero
distinct_from:
  leavitt-algebras-have-no-trdeg-two-subfields: that needs every nonzero p(a, b) invertible in L itself; this only needs every p(a, b) invertible in some nonzero overring (some module), which is strictly weaker, since non-units such as 1 + s_0 are invertible on a nonzero module.
  leavitt-algebras-contain-no-two-variable-polynomial-ring: that forbids k[a, b] outright and is open; this is a proved necessary condition on any k[a, b] that exists.
  leavitt-polynomial-pairs-move-to-the-nonnegative-part: that is a grading transfer; this is a localization condition with no grading.
  leavitt-isometry-centralizers-are-monogenic: that settles pairs containing a monomial isometry, one kind of universally singular element; this shows every pair must contain some universally singular element.
---

**ESTABLISHED** by `leavitt-polynomial-pairs-singular-element-proof` (unreviewed).

Call `c ∈ A` **universally singular** if the universal localization `A_c` (the universal ring inverting `c`) is `0`.
Equivalently, `c` acts non-bijectively on every nonzero left `A`-module: if `c` acts bijectively on `V ≠ 0` then
`A -> End_k(V)` inverts `c`, and conversely `V = A_c` works.

**Theorem.** Let `k` be a field and `A` a simple `k`-algebra with `pd_(A^e) A <= 1`. The instance used here
is `A = L_k(1,2)`, for every field `k`. Let `C ⊆ A` be a commutative subdomain with `k ⊆ C` and
`trdeg_k Frac(C) >= 2`, for example `C = k[a, b]` with `a, b` commuting and algebraically independent. Then:
1. the universal localization `A_Σ`, `Σ = C ∖ 0`, is the zero ring;
2. there is a single `p ∈ C ∖ 0` with `A_p = 0`, i.e. `p` is universally singular;
3. every multiple `pq`, `q ∈ C ∖ 0`, is universally singular too.

**Consequences for Q_2** (the NO side of Ara--Cortiñas Q5.7, and mechanism (i) of the `F_2[Z^4]` test case, at
`k = F_2` and `k = F_2(x, y)`).
- A witness `k[a, b] ⊆ L` must contain `p(a, b) ≠ 0` that is non-bijective on *every* nonzero `L`-module: the
  function module `F(X, k)`, `LC(X, k)`, every twisted Chen module, every ultraproduct of modules.
- Zero divisors and one-sided units are universally singular: `cx = 0, x ≠ 0` kills `x`, hence (simplicity) all
  of `A_c`; `vu = 1 ≠ uv` kills `1 - uv`.
- The condition is strictly stronger than non-invertibility. Let `X = {0,1}^N` and let `L` act on all functions
  `F(X, k)` by `(s_i f)(ω) = [ω_0 = i] f(σω)` and `(t_i f)(ω) = f(iω)`; the Leavitt relations hold pointwise.
  For `char k ≠ 2`, `c = 1 + s_0` is bijective on `F(X, k)`: `(cf)(ω) = f(ω) + [ω_0 = 0] f(σω)` is triangular in
  the number `m(ω)` of leading zeros, and at `0^∞` it is multiplication by `2`. So `L_c ≠ 0`. But `c` is not a
  unit of `L`: its unique preimage of `1` in `F(X, k)` takes the value `1` for `m(ω)` even and `0` for `m(ω)` odd,
  which is not locally constant at `0^∞`, so `c` is not onto `LC(X, k)`. For `char k = 2` use
  `c' = 1 + s_0 + s_0^2` instead: it is bijective on `F(X, k)` whenever `char k ≠ 3` (factor `3` at `0^∞`), and
  the preimage of `1` has values `1, 0, 0, 1, 0, 0, ...` along `m(ω) = 0, 1, 2, ...`, again not locally constant.
  Step 5 of the proof checks both.

So the homological field bound reaches past its stated form: what survives of Q5.7 lives entirely inside the
universally singular elements of `L` and their centralizers.
