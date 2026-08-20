---
rg: 2
id: signed-hecke-compatible-projection-atlas-for-nonce-bcs
kind: claim
title: A no-CE-trace BCS has a compatible algebraic projection atlas in one signed group corner
artifacts:
  - research/artifacts/signed-hecke-direct-trace-promotion-2026-08-20.md
distinct_from:
  character-rigid-signed-bcs-quotient: that asks for a quotient from a unique-trace corner onto the BCS algebra and must preserve character rigidity; this asks for a homomorphism in the opposite direction, from the BCS algebra into the canonical positive corner, so no source-trace classification is needed.
  bcs-projective-kernel-phase-compilation: that tries to compress each predicate to one projective scalar phase; this retains complete context projection partitions and asks for their shared marginals to agree.
---

Fix the finite BCS `B` supplied by `mipstar-bcs-tracial-nonru-exists`. Find a
finitely presented group `Gamma`, a finite subgroup `K<=Gamma`, and an
irreducible type `rho in Irr(K)` with `dim(rho)>1`, such that for
`q=z_rho` the corner `qC[Gamma]q` contains algebraic projections

```text
p_(c,a),       c a context, a in R_c,                         (SHA1)
```

satisfying the compatible projection-atlas equations `(BPA1)--(BPA3)`.
Equivalently, construct one unital star homomorphism

```text
A(B) -> qC[Gamma]q.                                          (SHA2)
```

The construction should give each projection and transport arrow by a finite
group-ring expression. Piecewise transport as in `(PGT1)--(PGT4)` is allowed;
no uniqueness of trace, quotient map, asymptotic decoder, or prescribed BCS
trace is required.

## Attempts

- The trivial finite-subgroup average is impossible by
  `augmentation-one-corner-retains-a-character`.
- `every-boolean-predicate-has-a-character-free-finite-type-block` constructs
  an exact seed partition for every context separately. The missing equation
  is precisely the cross-context marginal identity `(BPA3)` in one common
  corner.
- **Common local type is solved.**
  `all-bcs-contexts-share-one-hyperoctahedral-signed-type` puts every context
  in a copy of one hyperoctahedral group and one irreducible type, with equal
  corner trace and an explicit common number of coordinate atoms.  No
  dimension- or trace-balancing bridge remains at the local level.
- **Shared-variable rank balancing is solved.**
  `tracial-bcs-has-rational-balanced-hyperoctahedral-atlas` rationalizes the
  local marginals of any source trace and clears denominators.  Every overlap
  then admits an explicit sign-preserving coordinate permutation in the same
  `K_D` type.  These edge matchings cannot be made globally coherent:
  `coherent-balanced-context-permutations-would-give-a-ce-trace` would turn
  such a gauge into a finite-dimensional BCS representation.
- Single compressed group elements stay in the corner-unit stabilizer.
  `piecewise-group-transport-gives-corner-unitaries` proves that two or more
  group translates can repair domains and ranges exactly, but it does not
  choose a globally compatible finite transport quiver.
- Ordinary free products or Bass--Serre amalgams preserve independent context
  choices and therefore do not force `(BPA3)`. A successful construction
  needs nontrivial finite holonomy among the context partitions.
- **Returning to the finite root block is impossible.**
  `root-block-piecewise-transport-cannot-host-nonce-bcs` shows that if all
  transported context projections lie in `q_D C[K_D]q_D`, the atlas is a
  finite-dimensional BCS model and creates a CE trace.  Thus the live target
  is more specific: place isomorphic local `M_D` blocks as distinct algebraic
  subalgebras of the infinite corner and identify only their shared signed
  marginals.
- **Narrow live cell.**  The route
  `signed-hecke-balanced-holonomy-route` leaves only
  `signed-hecke-block-escaping-cycle-holonomy`: realize the residual chord
  transports by finite-support corner unitaries which preserve the one shared
  sign but move the remaining matrix block outside the finite root algebra.
