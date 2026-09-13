---
rg: 2
id: normalizer-image-of-type-a-actor-is-type-a
kind: claim
title: A type (A) actor enlarged by normalizing permutations with finitely presented image modulo the actor is again a type (A) actor
distinct_from:
  normalizer-extension-of-type-a-actor-is-a2-cover: that builds the non-faithful type [A_2] cover by a free group and proves the image is not finitely presented when Q/(Q∩Γ) is not; this is the converse, proving the image itself is a faithful type (A) actor when Q/(Q∩Γ) is finitely presented.
  stable-permutation-hnn-of-type-a-actor-is-type-a: that enlarges an actor by one permutation realizing an HNN extension, with a ping-pong condition; this enlarges it by any finitely generated group of normalizing permutations, where finite presentation of the quotient is the only condition.
---

**ESTABLISHED** by `normalizer-image-of-type-a-actor-is-type-a-proof`.

Let `Γ <= Sym(S)` be a faithful action of type (A)
(`type-a-action-gives-boone-higman-for-subgroups`). Let `Q <= N_(Sym(S))(Γ)` be
finitely generated, and suppose `Q/(Q ∩ Γ)` is finitely presented. Then the
permutation group `ΓQ <= Sym(S)` acts on `S` with type (A).

**Consequences for complexity.**
- `Q` is a finitely generated subgroup of `ΓQ`, so the word problem of `Q`
  substitutes into that of `ΓQ` at linear cost. By
  `twisted-brin-thompson-wp-equals-actor-orbit-problem`, the finitely presented
  simple group `SV_(ΓQ)` is at least as hard as `Q`.
- So `type-a-actors-with-arbitrarily-hard-word-problem` follows once, for every
  recursive `T`, some type (A) actor has a finitely generated normalizing group
  `Q` with finitely presented `Q/(Q ∩ Γ)` and word problem outside `F(T)`.
- The normalizing group need not carry a type (A) action of its own. It only has
  to act by permutations that preserve some oligomorphic finitely presented
  actor.

**Where the known actors stand.** These are attempt 5 of the open claim:
- **Thompson-type actors.** By Rubin's theorem the Cantor-space normalizer of
  `V` is `Aut(V)`. `Aut(V)` is reported to consist of rational homeomorphisms
  (Bleak--Cameron--Maissel--Navas--Olukoya; not re-read here). Its finitely
  generated subgroups then share the exponential bound of
  `rational-homeomorphism-subgroups-have-exponential-wp`.
- **Twisted Brin--Thompson actors.** Coordinate permutations normalizing the actor
  of `S` normalize `SV_G`, so hardness would be passed back to the actor's own
  normalizer.
- **Houghton actors.** A normalizing permutation must carry eventual translations
  to eventual translations. One therefore expects it to be eventually affine on
  the rays, giving a normalizer commensurable with the actor. This is not written
  out here.
