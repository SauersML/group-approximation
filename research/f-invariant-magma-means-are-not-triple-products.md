---
rg: 2
id: f-invariant-magma-means-are-not-triple-products
kind: claim
title: No re-association-invariant mean on the free magma is a triple product β^(β′^κ), so every Ellis-type product construction of an invariant mean for Thompson's F dies
distinct_from:
  free-binary-systems-carry-no-idempotent-mean: that kills idempotent means ν = ν^ν; this kills every F-invariant mean of the form β^(β′^κ) for arbitrary, unrelated means β, β′, κ, which includes ν^(ν^ν) and Moore's associative triples, and it reduces to that claim.
  free-magma-carries-an-idempotent-finitely-additive-measure: that is the refuted existence statement; this shows that no relaxation of it to a product of three means can serve Moore's Theorem 3.3 either.
  thompson-f-is-amenable: that is the root, equivalent to the existence of some F-invariant mean on the free magma; this excludes only those of triple-product form.
---

**Setting.** `T` is the free magma on one generator `1`, with product `^`. A *mean* is a finitely additive probability
measure on all subsets of `T`. For means put `μ^ν(X) = ∫ ν(X_s) dμ(s)`, where `X_s = {t : s^t ∈ X}`. This is Moore's
convention, verbatim in `free-binary-systems-carry-no-idempotent-mean`.

Moore's partial action of `F` on `T` (arXiv:1209.2063v1, quoted verbatim in the route
`thompson-f-amenable-via-idempotent-magma-measure`) is:
- `x_1·((a^b)^c) = a^(b^c)`, on `D_1 = (T^T)^T`;
- `x_2·(s^((a^b)^c)) = s^(a^(b^c))`, on `D_2 = T^D_1`.

A mean `γ` is *F-invariant* if `γ(D_1 ∩ D_2) = 1` and `γ(x_1·W) = γ(x_2·W) = γ(W)` for all `W` (with `x_i·W` the image
of `W ∩ D_i`). By the equivalence Moore quotes, such a `γ` exists iff `F` is amenable.

**Theorem (ESTABLISHED).** There are no means `β, β′, κ` on `T` such that `γ = β^(β′^κ)` is F-invariant.

Here the three factors are arbitrary and need not be related. The theorem covers:
- idempotents: `β = β′ = κ = ν`, with `ν^(ν^ν) = ν`;
- associative triples, meaning means with `(α^β)^γ = α^(β^γ)`, which are the relaxation Theorem 3.3's computation
  actually uses. Evaluating both sides on rectangles `A^B` gives `α^β = α` and `β^γ = γ`. So such a common value is
  the triple product `α^(β^γ)`;
- the fixed-point relaxation "`β^γ = γ` and `γ` is `x_1`-invariant".

Proof: `f-invariant-magma-means-are-not-triple-products-proof`. It reduces to
`free-binary-systems-carry-no-idempotent-mean`.

**Where every member dies.**
- *The invariant.* The factorisation of `γ` into independent left child, right-left grandchild and right-right
  grandchild.
- *Step 1.* `x_1`-invariance, tested on the sets `Y^T` and `(T^T)^C`, forces `β = β^β′` and `β′^κ = κ`.
- *Step 2.* `x_2`-invariance makes `κ = β′^κ` itself `x_1`-invariant. Step 1 applied to `κ` forces `β′ = β′^β′`.
- *Step 3.* `β′` is idempotent, and Moore's self-referential set `Z` kills it.

*Calibration.* With `x_1` alone the same steps are consistent. Take `β′ = δ_1`, `κ` a shift-invariant mean on the
right combs `1^(1^(⋯))`, and `β` a Markov–Kakutani fixed point of `μ ↦ μ^δ_1`. Then `β^(δ_1^κ)` is
`x_1`-invariant. So the kill uses the second generator essentially, as it must: `⟨x_1⟩ ≅ Z` is amenable.

**Why it matters.** Moore's route (arXiv:1209.2063 §3) built an invariant mean on `T` from the product structure of
`(Pr(T), ^)`. Such a mean is invariant because re-association permutes the factors of an iterated product. The
refutation of idempotents left open whether some other product of means, not a fixed point, could serve. This
theorem closes that door for every product of depth two on the right, which is the depth Theorem 3.3 uses. Any
invariant mean for `F` on `T` must have dependent right-spine factors.

## Attempts

- **2026-09-18 (swarm-0917-w7-w7-f-last1, minimal-counterexample).** Proved as above. The boundary is the depth-one
  form `γ = β^κ` with `κ` arbitrary.
  - What survives there: Step 2 still makes `κ` `x_1`-invariant.
  - What Step 1 then gives: `κ` has right-child marginal `κ` (test sets `(T^T)^C`) and `β = β^λ` on `T^T`, where
    `λ(X) = κ(X^T)` is the left-child marginal of `κ`.
  - Where it dies: no product structure of `κ` is available, so Step 1 cannot be iterated. Whether an F-invariant
    mean of the form `β^κ` exists when `F` is amenable is left open, and not filed as a node.
