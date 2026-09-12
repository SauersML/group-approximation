---
rg: 2
id: el3-of-infinite-rank-rings-not-linear-over-number-fields
kind: claim
title: Finite-index subgroups of EL_n(R), n >= 3, over a ring whose additive group has infinite rank are not linear over any number field
distinct_from:
  char-zero-algebra-unit-hosts-exclude-unipotents: that excludes simple unit-group hosts through congruence quotients; this excludes every faithful representation over a number field, host or not, through distortion of elementary matrices.
  algebraic-linear-groups-satisfy-boone-higman: that is the positive result over algebraic number fields; this shows its restriction-of-scalars route cannot reach EL_3 of a ring of positive transcendence degree through any abstract embedding.
  affine-self-similar-coordinate-rings-are-one-dimensional: that obstructs one construction, affine digit groups over transcendental coordinate rings; this obstructs every representation of the input group over a number field.
artifacts:
  - research/artifacts/bh-full-cantor-ca-host-2026-09-12.md
---

**ESTABLISHED.** Let `R` be an associative ring that is finitely generated as a
ring, and suppose its additive group has infinite torsion-free rank, that is,
`R ⊗ Q` is infinite-dimensional over `Q`. Let `n >= 3`, and let `Lambda` be a
finite-index subgroup of the elementary group `EL_n(R)`. Then for every `N` and
every number field `K` there is no injective homomorphism `Lambda -> GL_N(K)`.
Equivalently, `Lambda` is not isomorphic to a subgroup of `GL_N(Qbar)`.

The proof is the route `el3-infinite-rank-not-number-field-linear-proof`.

**Examples.**
- `R = Z[t_1, ..., t_d]` with `d >= 1`. So no finite-index subgroup of
  `EL_3(Z[t])` is linear over `Qbar`, although `EL_3(Z[t])` is linear over `Q(t)`.
- By Suslin's theorem `SL_n(Z[t]) = EL_n(Z[t])` for `n >= 3` (imported, not
  re-read), so the same holds for `SL_3(Z[t])`, the first open case of
  `char-zero-linear-groups-satisfy-boone-higman`.

**Consequences for Boone--Higman.**
- **No shortcut through number fields.** `algebraic-linear-groups-satisfy-boone-higman`
  (restriction of scalars, then Zaremsky's `GL_n(Q)` theorem) cannot reach
  `SL_3(Z[t])` or any of its finite-index subgroups through an abstract embedding
  into some `GL_N(Q)`, whatever `N`. Any host has to carry the transcendental
  parameter itself.
- **Local groups of eventually similar hosts.** Combined with
  `fw-subgroups-of-eventually-similar-groups-virtually-embed`, this excludes every
  host whose local vertex groups are linear over `Qbar`. See
  `el3-z-t-embeds-in-no-host-with-number-field-local-groups`.

**Mechanism.** Elementary matrices are quadratically distorted, so every faithful
representation over a number field makes them virtually unipotent. A root
subgroup is then a free abelian group of infinite rank inside a vector group of
finite rank.

**Scope.** The argument is classical in shape: distortion forces eigenvalues onto
the unit circle at every place, and Kronecker's theorem finishes. No novelty is
claimed. It is recorded because it pins down what the open part of the root
really requires. It says nothing about representations over fields of positive
transcendence degree, and nothing about groups without distorted root
subgroups of infinite rank.
