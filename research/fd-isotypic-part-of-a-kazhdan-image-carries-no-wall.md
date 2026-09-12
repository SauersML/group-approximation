---
rg: 2
id: fd-isotypic-part-of-a-kazhdan-image-carries-no-wall
kind: claim
title: The finite-dimensional isotypic part of a Kazhdan subgroup's image carries no relative wall, in any finite von Neumann algebra
distinct_from:
  commutant-no-growth: that counts linear dimension for a genuine finite-dimensional representation; this works inside an arbitrary finite von Neumann algebra, where the image algebra can be infinite-dimensional with infinitely many isotypic summands, and counts atom masses instead.
  relative-wall-commutant-growth: that equates a wall with properness of one inclusion of relative commutants, with no rigidity input; this proves the inclusion is an equality on the finite-dimensional isotypic part whenever the subgroup has property (T).
  compressor-growth-index-homomorphism: that uses the Pimsner--Popa index, which may be infinite; this uses no index and applies to infinite-index inclusions.
  transported-gap-masa-kills-leavitt-hs-models: that pushes a maximal abelian subalgebra out of the Kazhdan commutant using a commuting nonabelian subgroup; this uses no masa and no second subgroup, only the isotypic decomposition of the Kazhdan image.
---

**ESTABLISHED.** Let `Lambda <= G` be countable groups with `Lambda` having
property (T), let `t in G` satisfy `t Lambda t^(-1) <= Lambda`, and let
`sigma : G -> U(M)` be a homomorphism into a finite von Neumann algebra
`(M,tau)` with faithful normal tracial state. For each finite-dimensional
irreducible representation `rho` of `Lambda` let `p_rho in C*(Lambda)` be its
central projection, and put

```text
z = sum_rho sigma(p_rho)          (the finite-dimensional isotypic part of sigma|Lambda).
```

Then

```text
Ad sigma(t)(z) = z,       sigma(t Lambda t^(-1))'' z = sigma(Lambda)'' z,
(M cap sigma(Lambda)') z = (M cap sigma(t Lambda t^(-1))') z.              (FIW1)
```

So a relative wall in the sense of `relative-wall-commutant-growth` is
supported on `1 - z`, the part of `sigma|Lambda` with no finite-dimensional
subrepresentation. No approximation, trace condition on `sigma`, or size
hypothesis is used.

**What it does and does not reach.** For a canonical (trace-preserving)
model, `sigma|Lambda` is contained in a multiple of the regular representation
of the infinite group `Lambda`, so `z = 0` and `(FIW1)` is vacuous; the
open branch of `kt-centralizer-normalization-hs` lives entirely on `1 - z`.
The statement bites for non-canonical models, which matter because
`ce-stabilizer-criterion-needs-no-trace` shows that relative embeddability
can be witnessed in any Connes-embeddable target with no trace condition,
and for targets in which `sigma(Lambda)''` is forced to be atomic
(`kazhdan-images-in-haagerup-algebras-are-atomic`).

DERIVATION
fd-isotypic-no-wall-proof
