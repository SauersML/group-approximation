---
rg: 2
id: rational-k1-detection-forces-infinite-order-unit-class-proof
kind: route
title: A torsion unit class gives a stable module isomorphism R^s ≅ R^(s+t), which makes rational powers elementary
target: rational-k1-detection-forces-infinite-order-unit-class
requires:
  - ibn-failure-makes-rational-scalars-elementary
---

**Step 1: from `K_0` to modules.** `K_0(R)` is the Grothendieck group of finitely generated
projective right `R`-modules. `[P] = [P']` means `P ⊕ R^s ≅ P' ⊕ R^s` for some `s >= 0`.
So `t[R] = 0 = [0]` gives `R^t ⊕ R^s ≅ R^s`, that is, `R^s ≅ R^(s+t)`. Here `s >= 1`, since
`R^t ≇ 0` for `R ≠ 0`.

**Step 2: elementary rational powers.** Apply `ibn-failure-makes-rational-scalars-elementary`,
part 1, with `m = m' = s`, `k = t` and `N = 2`. For every `λ ∈ Q^x`,
`λ^t I_(2s) ∈ E_(2s)(R) ⊆ E(R)`, so the class of `λ^t I_(2s)` in `K_1(R) = GL(R)/E(R)` is `0`.

**Step 3: that class is `ι(λ^(2st))`.** In `K_1(R)`, a block-diagonal matrix has the sum of
the classes of its blocks. So the class of `μ I_M` is `M·ι(μ)`, and it equals `ι(μ^M)`
because `ι` is a homomorphism. With `μ = λ^t` and `M = 2s`, this gives `ι(λ^(2st)) = 0`
for all `λ`.

**Step 4.** `(Q^x)^(2st)` contains the `2st`-th powers of all primes, which are
independent, so it is not finitely generated. Neither is `ker ι`, which contains it. Part 2
is the contrapositive. ∎
