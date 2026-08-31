---
rg: 2
id: whitehead-injective-torsion-free-embedding
kind: claim
title: A Whitehead-injective torsion-free Higman embedding
distinct_from:
  torsion-free-higman-embedding: that claim is the embedding of groups alone and is now established from Chiodo Theorem 2.2; this one demands in addition that the induced map on Whitehead groups be injective, which no known construction provides and which is the entire remaining gap on the finitely-presented route.
  whitehead-vanishing-torsion-free: that is the conjecture itself, an assertion that certain groups are zero; this asserts nothing is zero -- it asks for injectivity of a comparison map, and is consistent with every Whitehead group in sight being nonzero.
  whitehead-vanishing-finitely-presented-torsion-free: that asserts vanishing for finitely presented groups; this asserts a property of embeddings into them and would be needed even if that vanishing were already known -- indeed it is exactly what would then be missing.
  whitehead-vanishing-recursively-presented-torsion-free: that is the vanishing statement for the source class of these embeddings; this is the transfer property of the embeddings themselves. Together they give that claim, which is why they are the two prerequisites of one route and not variants of each other.
  whitehead-vanishing-universal-test-group: that is a vanishing statement for one specific restricted product; this is a property required of a family of embeddings, and neither the group nor the assertion is shared.
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
---

Every finitely generated recursively presented torsion-free group `K` admits
an embedding `K -> H` into a finitely presented torsion-free group such that

    Wh(K) -> Wh(H)

is **injective**.

Open, and it is the single missing step in the finitely-presented route to
`whitehead-vanishing-torsion-free`.  The group-theoretic half is finished:
Chiodo's Theorem 2.2 supplies the embedding and preserves torsion-freeness
(`torsion-free-higman-embedding`), and the finite-pattern refinement
transplants an invertible matrix together with its inverse
(`finite-torsion-free-pattern-realizable-finitely-presented`).  Neither
carries any information about `K_1`.

## Attempts

All three known repairs fail, each for a different reason, and the failures
are the informative part.

*Retraction.*  Asking instead for the embedding to be split as a group
embedding is too strong to be true in general: a retract of a finitely
presented group is finitely presented, and the groups being embedded here
need not be.

*Transplantation.*  Realizing the finite equation-and-inequation pattern of
`A` and `A^-1` inside `H` gives `Atilde` in `GL_n(ZH)` with the same
coefficient pattern, but if `Wh(H) = 0` the resulting elementary
factorization of `Atilde` may use group elements of `H` far outside the
imported pattern, and the construction supplies no homomorphism `H -> K`
returning them.  The available diagram is

    P -> Ptf -> H        and        Ptf -> G,

with the two arrows leaving `Ptf` in different directions.  Functoriality
gives `Wh(Ptf) -> Wh(H)` and nothing about its kernel.

*Going the other way.*  The one direction that does work is stopping at
`Ptf`, where the comparison map points back at `G`; that is
`whitehead-vanishing-recursively-presented-torsion-free`, and it is why this
claim is quantified over finitely generated recursively presented groups --
which makes it exactly strong enough, together with
`whitehead-vanishing-finitely-presented-torsion-free`, to close the
conjecture.

## Why Chiodo's stronger universal group does not remove it

Chiodo Theorem 3.9 gives one finitely presented torsion-free group containing
every countably generated recursively presentable torsion-free group.  Same
obstruction: subgroup inclusion supplies a map on Whitehead groups, not its
injectivity.  By contrast, Lueck's reduction of the *full* Farrell--Jones
conjecture to one universal finitely presented group succeeds because that
conjecture is inherited under subgroups and directed colimits.  The bare
assertion `Wh = 0` has no such inheritance package, which is the structural
reason this gap is not a technicality.
