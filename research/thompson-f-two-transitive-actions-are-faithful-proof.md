---
rg: 2
id: thompson-f-two-transitive-actions-are-faithful-proof
kind: route
title: Normal subgroups of F contain [F,F], and transitive abelian groups are regular
target: thompson-f-two-transitive-actions-are-faithful
requires: []
---

Input (standard): every nontrivial normal subgroup of `F` contains `[F,F]`
(Cannon–Floyd–Parry, *Introductory notes on Richard Thompson's groups*,
Enseign. Math. 42 (1996), Theorem 4.3: every proper quotient of `F` is
abelian), and `[F,F]` is simple and infinite.

1. Let `N` be the kernel of the action. If `N ≠ 1` then `N ⊇ [F,F]`, so the
   image `A` of `F` in `Sym(Ω)` is abelian. A transitive abelian permutation
   group is regular: if `a` fixes `ω`, then `a` fixes `bω` for all `b ∈ A`,
   since `a(bω) = b(aω) = bω`, so `a = 1`. But 2-transitivity makes the
   stabilizer of `ω` transitive on `Ω \ {ω}`, which has at least two points, so
   the stabilizer is nontrivial. Contradiction, so `N = 1`.
2. A finite `Ω` would give a homomorphism from `F` to a finite group, with
   nontrivial kernel since `F` is infinite. So the image would be abelian,
   which step 1 excludes.
3. A 2-transitive action is primitive, and a nontrivial normal subgroup of a
   primitive group is transitive: its orbits form an `F`-invariant partition,
   so they are singletons or the whole of `Ω`. Singletons would mean
   `[F,F] ≤ N = 1`, which is false. So `[F,F]` is transitive.
