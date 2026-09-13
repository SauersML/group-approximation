---
rg: 2
id: pbh-wreath-closure-via-free-relative-automorphism-orbits
kind: route
title: Pull the lamps back to a free cover of X, push them into the relative automorphism actor along free orbits, and use the type (A) lamp wreath
target: permutational-boone-higman-closed-under-wreath-products
requires:
  - type-a-actors-closed-under-type-a-lamp-wreaths
  - pbh-groups-act-freely-in-relative-automorphism-actors
  - type-a-action-gives-boone-higman-for-subgroups
artifacts:
  - research/artifacts/solve-bh-free-solvable-2026-09-13.md
---

Direct proof (2026-09-13, lane `solve-bh-free-solvable`). Not independently reviewed.
Conventions: `(g·f)(u) = f(g^(-1) u)` and `(f, g)(f', g') = (f·(g·f'), gg')`.

**0.** If `A = 1` then `A wr_X G ≅ G`, which is in `B_A`. Assume `A ≠ 1`.

**1. Lamp actor.** `A ≤ Λ` for some `Λ` acting on a set `Y` with type (A). Then
`Λ ≠ 1`.

**2. Top actor.** By `pbh-groups-act-freely-in-relative-automorphism-actors` there
are:
- `G ≤ M`;
- `Γ = Aut_M(M * F_2)` acting on `S = Hom_M(M * F_2, M)` with type (A);
- an injective homomorphism `τ : M -> Γ` such that `τ(G)` acts freely on `S` with
  infinitely many orbits.

**3. A free cover of `X`.**
- Write `X = ⊔_(i ∈ I) G·x_i` with `I` countable, and `K_i = Stab_G(x_i)`, which is
  finite.
- Let `X~ = G × I` with `g·(h, i) = (gh, i)`, a countable free `G`-set.
- Let `π(h, i) = h·x_i`. Then `π` is `G`-equivariant and surjective, and each fibre
  has `|K_i|` points.
- Pullback `f -> f ∘ π` maps `A^(X)` to `A^(X~)`:
  - finite fibres keep supports finite;
  - surjectivity of `π` makes the map injective;
  - it is multiplicative;
  - it is equivariant, since `(g·(f ∘ π))(u) = f(π(g^(-1)u)) = f(g^(-1)π(u)) = (g·f)(π(u))`.
- So `(f, g) -> (f ∘ π, g)` is an injective homomorphism
  `A wr_X G -> A wr_(X~) G`.

**4. Into the actor set.**
- By the consequence in `pbh-groups-act-freely-in-relative-automorphism-actors`
  there is a `G`-equivariant injection `ι : X~ -> S`, where `G` acts on `S` through
  `τ`.
- Define `ι_* : A^(X~) -> Λ^(S)` by `(ι_* f)(ι(u)) = f(u)`, with value `1` off
  `ι(X~)`. It is injective and multiplicative.
- It is equivariant. On `ι(X~)`,
  `(τ(g)·ι_* f)(ι(u)) = (ι_* f)(ι(g^(-1)u)) = f(g^(-1)u) = (ι_*(g·f))(ι(u))`.
  Off `ι(X~)` both sides are `1`, because `ι(X~)` is `τ(G)`-invariant.
- So `(f, g) -> (ι_* f, τ(g))` is an injective homomorphism
  `A wr_(X~) G -> Λ wr_S Γ`.

**5. Conclusion.** By `type-a-actors-closed-under-type-a-lamp-wreaths`,
`Λ wr_S Γ` acts on `S × Y` with type (A). The composite of steps 3 and 4 embeds
`A wr_X G` in it, so `A wr_X G ∈ B_A`. The consequences are
`type-a-action-gives-boone-higman-for-subgroups` (Zaremsky, Corollary B). `∎`

**Where finiteness of stabilizers is used.** Only in step 3, to keep pulled-back
supports finite. Every stabilizer of `τ(G)` on `S` is trivial, so lamps over an
infinite stabilizer cannot be pushed into `S` along an orbit.
