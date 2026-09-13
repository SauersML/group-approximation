---
rg: 2
id: fp-simple-groups-no-rational-polytope-exchange-proof
kind: route
title: Rational polytope exchange groups are LEF, rational toral rotation codings embed there, and finitely presented LEF groups are residually finite
target: fp-simple-groups-have-no-rational-polytope-exchange-action
requires:
  - rational-polytope-exchange-groups-are-lef
  - finitely-presented-lef-groups-are-residually-finite
---

**Statement 1.** Let `S` be finitely presented, infinite and simple, and `ρ` a homomorphism
from `S` to the rational polytope exchanges of `T^k`.
1. `ker ρ` is normal, so it is trivial or `S`. Suppose it is trivial. Then `ρ(S)` is a
   finitely generated group of rational polytope exchanges isomorphic to `S`.
2. By `rational-polytope-exchange-groups-are-lef`, `S` is LEF.
3. By `finitely-presented-lef-groups-are-residually-finite`, `S` is residually finite.
4. A nontrivial residually finite group has a proper normal subgroup of finite index. `S` is
   simple, so that subgroup is trivial and `S` is finite. That is a contradiction, so `ρ` is
   trivial.

**Statement 2.** Take the notation of the claim. The shift is `(m·c)(n) = c(n + m)`, so
`m·c_z = c_({z + m·θ})`.
1. **Cocycles.** Every `g ∈ [[Z^d ~ X]]` has a continuous `κ_g : X -> Z^d` with
   `g(x) = κ_g(x)·x`.
   - It is unique because the action on `X` is free.
   - Uniqueness gives `κ_(gh)(x) = κ_g(h(x)) + κ_h(x)`.
   - By compactness, `κ_g(x)` depends only on `x|B(R)` for some `R`.
2. **The map.** Put `ψ_g(z) = {z + κ_g(c_z)·θ}` for `z ∈ [0, 1)^k`.
   - `c_z|B(R)` is the tuple `(f({z + n·θ}))_(|n| <= R)`.
   - The set `{z : f({z + n·θ}) = a}` is the preimage of the rational polyhedral set `f^(-1)(a)`
     under `z -> {z + n·θ}`. Splitting by the floor vector `⌊z + n·θ⌋`, which takes finitely
     many values, writes it as a finite union of basic sets. Their normals are those of the
     fibres together with `±e_i`, all integer vectors, and their offsets are shifted.
   - So the sets `{z : c_z|B(R) = π}` are rational polyhedral and partition `[0, 1)^k`, and on
     each of them `ψ_g` is the translation by `κ_g(π)·θ` followed by fractional parts.
3. **Homomorphism.** Let `z' = ψ_h(z)`. Then `c_(z') = κ_h(c_z)·c_z = h(c_z)`, so
   `ψ_g(ψ_h(z)) = {z + (κ_h(c_z) + κ_g(h(c_z)))·θ} = {z + κ_(gh)(c_z)·θ} = ψ_(gh)(z)`.
   - Also `ψ_1 = id`.
   - So `ψ_(g^(-1))` inverts `ψ_g`, and each `ψ_g` is a rational polytope exchange.
4. **Injectivity.** Suppose `ψ_g = id`.
   - Then `κ_g(c_z)·θ ∈ Z^k` for every `z`, so `κ_g(c_z) = 0` by the hypothesis on `θ`, and
     `g(c_z) = c_z`.
   - `g` is continuous and `{c_z}` is dense in `X`, so `g = id`.
5. **Conclusion.** `g -> ψ_g` embeds `[[Z^d ~ X]]` in the rational polytope exchanges of `T^k`.
   - Any finitely presented infinite simple subgroup would act faithfully by rational polytope
     exchanges, which Statement 1 excludes.
   - An infinite simple `D([[Z^d ~ X]])` or `A([[Z^d ~ X]])` is finitely generated for minimal
     `X` by the cited node, and by what was just shown it is not finitely presented. ∎
