---
rg: 2
id: order-p-automorphism-kk-cyclotomic-structure-proof
kind: route
title: Identify the Z crossed product by a periodic automorphism with a mapping torus, then run Pimsner--Voiculescu and cyclotomic arithmetic
target: order-p-automorphism-kk-cyclotomic-structure
requires: []
---

Notation as in the claim: `D = C ⋊_β Z_p` with implementing unitary `v`
(`v^p = 1`), `ω = e^(2πi/p)`, and `σ ∈ Aut(D)` the dual automorphism
`σ(c) = c`, `σ(v) = ω v`.

**Step 1: `C ⋊_β Z ≅ M_σ`.**  Let `u` be the implementing unitary of `C ⋊_β Z`.
Define `Φ : C ⋊_β Z → C(T, D)` by `Φ(c) = c ⊗ 1` and `Φ(u) = (z ↦ z v)`.  This is
covariant, since `(z v) c (z v)^* = β(c)`, so `Φ` exists.

* *Φ is injective.*  Let `γ` be the dual circle action on `C ⋊_β Z` and
  `(ρ_ζ f)(z) = f(ζ z)`.  Then `Φ ∘ γ_ζ = ρ_ζ ∘ Φ`.  Both algebras carry faithful
  conditional expectations onto the fixed points: `C` on the left (reduced
  crossed product, `Z` amenable), constant functions on the right.  `Φ` is
  injective on `C`.  So `Φ(a) = 0` gives `E(a^*a) = 0`, hence `a = 0`.
* *The image.*  The image is `B = {f ∈ C(T, D) : f(ω z) = σ(f(z))}`.  Every
  `Φ(c u^n) = (z ↦ c v^n z^n)` lies in `B`.  Conversely, let `f ∈ B` have Fourier
  coefficients `d_m ∈ D`.  Then `σ(d_m) = ω^m d_m`, so `d_m ∈ C v^m`, and the
  Fejér means of `f` lie in `Φ(C ⋊_β Z)`.  The image is closed, so it is `B`.
* *Mapping torus.*  Restricting `f ∈ B` to the arc `z = e^(2πis/p)`,
  `s ∈ [0, 1]`, gives `g(s)` with `g(1) = σ(g(0))`.  Conversely such a `g` extends
  uniquely by `f(ω^k z) = σ^k(f(z))`, consistently because `σ^p = id`.  So
  `B ≅ M_σ = {g ∈ C([0,1], D) : g(1) = σ(g(0))}`.

**Step 2: contractibility.**  Evaluation at `0` gives
`0 → SD → M_σ → D → 0`.  The map `d ↦ (s ↦ (1 − s) d + s σ(d))` is a
completely positive contractive lift, so the extension is semisplit.  In the
exact sequence `KK(E, SD) → KK(E, M_σ) → KK(E, D)` both outer groups vanish, for
every `E`.  With `E = M_σ` this gives `[id] = 0`.

**Step 3: `1 − t` is invertible.**  The Pimsner--Voiculescu six-term sequence in
the second variable of KK (Pimsner--Voiculescu 1980; Kasparov's KK version)
contains `KK^*(E, C) --(1 − β_*)--> KK^*(E, C) → KK^*(E, C ⋊_β Z)`.  The theorem
number was not re-read here.  The third group vanishes by Step 2, in both
parities, so `1 − β_*` is bijective on `KK^*(E, C)` for every `E`.  At `E = C`,
the map `y ↦ y(1 − t)` is bijective on `R`.  Surjectivity gives `x` with
`x(1 − t) = 1`.  Then `((1 − t)x − 1)(1 − t) = (1 − t) − (1 − t) = 0`, and
injectivity gives `(1 − t)x = 1`.  So `1 − t` is a unit.

**Step 4: the norm vanishes.**  `0 = 1 − t^p = (1 − t)(1 + t + ⋯ + t^(p−1))`,
and `1 − t` is a unit.  Since `Φ_p(x) = 1 + x + ⋯ + x^(p−1)` for prime `p`,
`x ↦ t` induces a ring map `Z[x]/(Φ_p) ≅ Z[ζ_p] → R`, with commutative image.

**Step 5: `p` is invertible.**  In `Z[ζ_p]`, `p = Φ_p(1) = ∏_(k=1)^(p−1) (1 − ζ^k)`,
so `p · 1 = ∏_k (1 − t^k)` in `R`.  For `1 ≤ k < p` pick `j` with `jk ≡ 1 (mod p)`.
Then `1 − t = 1 − (t^k)^j = (1 − t^k)(1 + t^k + ⋯ + t^(k(j−1)))`.  All factors
lie in the commutative subring `Z[t]`, and `1 − t` is a unit, so `1 − t^k` is a
unit.  Hence `p · 1` is a unit.

**Step 6: modules.**  `KK^*(D', C)` is a left `R`-module by Kasparov product,
and `KK^*(C, D')` is a right one.  The units `p` and `1 − t` of `R` act
invertibly on both.  `D' = C` in the first gives K-theory, and `D' = C` in the
second gives K-homology.  `β`-invariant classes are killed by `1 − β_*`, and
coinvariants are the cokernel of `1 − β_*`, so both vanish.

**Model tests.**  The cyclic shift on `C^p` fails the hypothesis and fails the
conclusion (see the claim).  The trivial action on `O_2` gives `O_2^p`, where
everything is zero.  Barlak--Szabó's `γ : Z_p ↷ O_2` (their Proposition 4.14,
crossed product KK-equivalent to `M_(p^∞)^(p−1)`) has
`K_0 = Z[1/p]^(p−1) ≅ Z[ζ_p, 1/p]`, with the dual action as multiplication by
`ζ_p`.  That is the rank-one free module over the ring in Step 5, as the claim
predicts.
