---
rg: 2
id: algebraic-tarski-for-steinberg-algebras-proof
kind: route
title: Proof of the algebraic Tarski chain - the type semigroup to V(R) bridge, faithful rank functions force stable finiteness, and Tarski with minimality gives an invariant measure
target: algebraic-tarski-for-steinberg-algebras
requires:
  - rainone-sims-tarski-alternative-for-monoids
  - abbl-type-semigroup-states-extend-to-invariant-measures
  - steinberg-algebra-simple-iff-minimal-effective
artifacts:
  - research/artifacts/un-algebraic-tarski-2026-09-13.md
---

Full derivation in the artifact, Sections 1–2 (unreviewed).

**The bridge.** `ι : S(𝒢) → V(R)`, `[U] ↦ [1_U R]`, is an order-preserving monoid homomorphism for
every field `k`: a compact open bisection `B` gives `1_B 1_{B^{-1}} = 1_{r(B)}` and
`1_{B^{-1}} 1_B = 1_{s(B)}`, so `[1_{s(B)}] = [1_{r(B)}]`; disjoint unions go to orthogonal sums and
levels of `X × ℕ` to matrix sizes. Landed independently by `un-paradox` inside
`no-invariant-measure-steinberg-elementary-no-mf-quotient`.

**Step 1 (rank ⟹ stably finite).** Let `rk` be a nonzero Sylvester matrix rank function. If `R` is
simple then `{a : rk(a) = 0}` is a proper two-sided ideal, hence `0`, so `rk` is faithful; assume
faithfulness. If `AB = I_n` then `n = rk(I_n) ≤ min(rk A, rk B) ≤ n`, and `B(AB) = B` gives
`rk(B) ≤ rk(BA)`, so the idempotent `e = BA` has `rk(e) = n`. Under the Malcolmson–Schofield
correspondence `rk` is the matrix form of a module rank function, and `R^n = eR^n ⊕ (1-e)R^n` gives
`rk(e) + rk(I_n - e) = n`. So `rk(I_n - e) = 0` and `BA = I_n` by faithfulness. This holds at every
matrix size, so `R` is stably finite.

**Step 2 (stably finite ⟹ `θ` completely non-paradoxical).** Contrapositive. If `(n+1)θ ≤ nθ` then
`ι` gives `(n+1)[1] ≤ n[1]` in `V(R)`, so there are `x ∈ M_{n+1,n}(R)`, `y ∈ M_{n,n+1}(R)` with
`xy = I_{n+1}` and `yx = p ≤ I_n` idempotent. Padding by a zero row and column to `x̃, ỹ ∈ M_{n+1}(R)`
gives `x̃ỹ = I_{n+1}` and `ỹx̃ = diag(p,0) ≠ I_{n+1}`, whose last diagonal entry is `0`. So
`M_{n+1}(R)` is not directly finite.

**Step 3 (complete non-paradoxicality ⟺ invariant measure, `𝒢` minimal).** An invariant probability
measure gives a state `ν` on `S(𝒢)` with `ν(θ) = 1`, so `θ` is not paradoxical by the Tarski
alternative `rainone-sims-tarski-alternative-for-monoids`. Conversely that theorem supplies a
nontrivial state `ν` with `ν(θ) = 1`. Minimality makes it finite and faithful on nonempty compact
opens: the sets `r(B)` over compact open bisections `B` with `s(B) ⊆ U` cover the compact `X`, so
`θ ≤ m[U]` and `0 < 1/m ≤ ν(U) ≤ 1`. Then `ν|_{K(X)}` is a finitely additive invariant probability
measure on the clopen algebra of a compact totally disconnected space, where finite additivity is
countable additivity because a clopen set has no infinite disjoint clopen cover; it extends to an
invariant Borel probability measure by
`abbl-type-semigroup-states-extend-to-invariant-measures`.

**Simplicity and automatic faithfulness.** `steinberg-algebra-simple-iff-minimal-effective` gives
simplicity of `R` for minimal effective `𝒢`, which is what makes a nonzero rank function faithful in
Step 1.

Standard inputs used and not re-derived here: the Malcolmson–Schofield matrix–module rank
correspondence, and subadditivity of Sylvester matrix rank functions.
