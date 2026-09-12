---
rg: 2
id: ce-stabilizer-criterion-needs-no-trace
kind: claim
title: Scalar relative embeddability is a commutation stabilizer in some Connes-embeddable target, with no trace condition on the representation
distinct_from:
  commutation-stabilizers-are-relatively-embeddable: that requires a canonical trace-preserving copy of the group algebra; this allows any homomorphism into any Connes-embeddable finite algebra, not necessarily injective and with any trace, and restores canonicity by tensoring with the regular representation.
  relative-embedding-is-commutant-separation: that characterizes relative embeddability through subgroup-central projections in canonical models; this removes the canonical-model requirement from the positive direction and supplies the stable-letter witness in the converse.
  rigid-compression-defect-normalization-dichotomy: that equates normalization of Kazhdan centralizers with triviality of rigid defects across approximation classes; this is an exact criterion for relative embeddability of one subgroup, with no rigidity hypothesis.
---

**ESTABLISHED.** Let `Lambda <= G` be countable groups with `G` hyperlinear.
The following are equivalent.

1. `L(Lambda) <= L(G)` is relatively embeddable over the scalars.
2. There are a finite von Neumann algebra `(M,tau)` that is Connes
   embeddable, a homomorphism `sigma : G -> U(M)`, and a countable family
   `(x_i) subset M` with

   ```text
   {g in G : [sigma(g), x_i] = 0 for all i} = Lambda.                 (CST1)
   ```

   No relation between `tau o sigma` and the canonical trace is required, and
   `sigma` need not be injective.

In `2 => 1` a single element suffices on the other side: `M = L(H)` for the
centralizer HNN group `H = G *_Lambda (Lambda x Z)`, `sigma` the inclusion, and
`x` the stable letter.

**Why it is useful.** Every hyperlinearity problem in the coset family of
`binary-free-and-ordinary-coset-wreaths-share-hyperlinearity` becomes the
search for one Connes-embeddable target in which `Lambda` is an exact
commutation stabilizer. The canonical trace, which is the hard part of every
hyperlinearity construction, is supplied for free by `lambda tensor sigma`.
The same tensoring moves any relative wall of `sigma` into a canonical model,
so walls may be looked for in non-canonical models.

The search space is not free of obstructions:
`haagerup-targets-carry-no-relative-wall` excludes every target in which the
Kazhdan image is Haagerup, and `kt-normalizing-witnesses-centralize-compressors`
excludes witnesses that normalize the group.

DERIVATION
ce-stabilizer-criterion-proof
