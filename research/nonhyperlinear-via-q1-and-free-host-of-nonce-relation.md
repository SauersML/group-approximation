---
rg: 2
id: nonhyperlinear-via-q1-and-free-host-of-nonce-relation
kind: route
title: A free host of the fixed non-CE relation, together with CE covariant models for hyperlinear actions, makes the host's actor non-hyperlinear
target: non-hyperlinear-group
requires:
  - nonce-relation-admits-free-host
  - hyperlinear-group-actions-have-ce-covariant-models
  - nonce-relation-hosts-force-root-or-q1-failure
  - free-action-covariant-models-contain-the-crossed-product
---

**Route.**
* `nonce-relation-admits-free-host` gives a countable `Lambda`, an essentially free pmp action `Lambda ↷ (Z, zeta)`,
  and a class-bijective placement of the Manzoor or property-(T) relation `R` into `R_Lambda(Z)`.
* Item 1 of `nonce-relation-hosts-force-root-or-q1-failure` gives a trace-preserving embedding of `L(R)` in a corner
  of `L^infinity(Z) ⋊ Lambda`. So this crossed product is not CE, since `L(R)` is not.
* If `Lambda` were hyperlinear, Q1 = `hyperlinear-group-actions-have-ce-covariant-models` would give a CE covariant
  model of this essentially free action. By `free-action-covariant-models-contain-the-crossed-product` item 1, that
  model contains the crossed product, which is a contradiction.
* Hence `Lambda` is a countable non-hyperlinear group.

The placement prerequisite can be replaced by "some action with finite stabilizers generates `R`". Item 3 of the
hosting claim then gives the same non-CE crossed product for that actor.

**Why the prerequisites fail independently.**
* **Q1 can fail while `R` has no host.** Q1 is a permanence statement about hyperlinear groups. Its failure (for
  example a non-hyperlinear Kun–Thom wreath, `hyperlinear-nonsofic-via-ce-covariant-models`) says nothing about
  placing `R`.
* **`R` can have no host while the root holds.** A free host of `R` is a measured orbit-equivalence placement of one
  fixed relation. A non-hyperlinear group elsewhere gives hosts only to its own relations, not to `R`. Class-bijective
  placements are rigid in general, as the Popa-type results in
  `kazhdan-bernoulli-product-seed-stabilizers-embed-in-host` show.
* **What each side excludes.** The placement is excluded for every actor where Q1 is known: amenable-by-virtually-free
  and free actors, by item 5 of the hosting claim. So the host's actor must lie outside every class where Q1 is
  currently proved. Under Q1 this is necessary, because the actor is then non-hyperlinear.

**Relation to the other Q1 routes.** Both this route and `nonhyperlinear-via-full-subgroup-covariant-models` use Q1.
That route needs a subgroup inside `[R]` whose action has no CE model. This route needs a free action outside `R`
into which `R` embeds class-bijectively. Q2 of that route is about subgroups of the full group of `R`, and this
route's placement is about overgroups of `R` in free relations. Neither implies the other as far as is known.
