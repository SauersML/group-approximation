---
rg: 2
id: o2-kkg-endomorphism-ring-acts-on-central-sequence-k-theory
kind: claim
title: Does KK^G(E, E) act on the equivariant K-theory of the central sequence algebra of an outer Z/p-action on O_2 with contractible crossed product, making p invertible there
distinct_from:
  o2-central-sequence-k-theory-bi-cyclotomic-transfer: that proves a Z[zeta_p] tensor Z[zeta_p]-module structure on K_* of the fixed central sequences by transfer, with p not inverted; this asks whether the whole ring KK^G(E, E), in which p is invertible, acts compatibly.
  zp-o2-generator-kk-class-is-twisted-asymptotic-innerness: that splits E into Galois components inside KK^G(E, E); this asks whether that splitting passes to the central sequence K-theory.
---

**OPEN.**  Let `p` be prime and `G = Z/p`.  Let `α : G ↷ O_2` be pointwise
outer with `O_2 ⋊_α G ≅ O_2`, and write `E = (O_2, α)`, `A = O_2`,
`F = A_∞ ∩ A'`, `M = K_0(F ⋊_(α_∞) G)`.

**Question.**  Is there a unital ring homomorphism `T : KK^G(E, E) → End(M)`
with these two properties?
- `T(χ·1_E)` is the `R(G)`-module structure of equivariant K-theory.
- `T([φ])` is induced by `φ` for unital equivariant endomorphisms `φ`, as
  described below.

**Consequences if yes.**  By `zp-algebras-with-contractible-restriction-are-cyclotomic`
and `zp-o2-generator-kk-class-is-twisted-asymptotic-innerness`:
- `p` is invertible on `M`;
- `M = ⊕_(k ∈ F_p^×) T(e_k) M`, and on `T(e_k) M` the generator acts as
  `χ^k`.

That would remove the inversion of `p` in item 4 of
`o2-central-sequence-k-theory-bi-cyclotomic-transfer`.  It would not decide
detection.  `T(θ)` sends the averaging class `[e_1]` to the class of the twisted
averaging projection of the implementing cocycle, and for a phantom
`KK^G(E, E) ≠ 0`.

## Attempts

* **Construction (lane ex2-uct-unit-class-cohomology, 2026-09-13).**
  - **Realize `x` by an endomorphism.**  Item 3 of
    `zp-o2-contractible-crossed-product-only-coboundaries` realizes every
    `x ∈ KK^G(E, E)` by a unital equivariant endomorphism `φ`.
  - **Implement `φ` on `A`.**  Unital endomorphisms of `O_2` are approximately
    unitarily equivalent to `id`.  So `φ = Ad(v)` on `A` for some
    `v ∈ U(A_∞)`.
  - **The induced map.**  `Φ(x) = v^* φ_∞(x) v` maps `F` to `F`.  It satisfies
    `α_g ∘ Φ = Ad(z_g^*) ∘ Φ ∘ α_g` with `z_g = v^* α_g(v) ∈ U(F)`, a cocycle.
  - **Crossed product.**  `x λ_g ↦ Φ(x) z_g λ_g` is a unital \*-homomorphism
    of `F ⋊ G`.  Changing `v` to `v w`, with `w ∈ U(F)`, conjugates it by `w^*`,
    so the map on `M` is well defined.
  - **Multiplicativity.**  The implementer of `φ ∘ φ'` is `φ_∞(v') v`, and
    `Φ_(φφ') = Φ_φ Φ_(φ')`.
* **Gaps, where it stops.**
  - *Independence of the representative.*  Gabe--Szabó Theorem 5.8 makes two
    endomorphisms with equal classes asymptotically unitarily equivalent,
    pointwise on `A`.  Moving this to `φ_∞` on sequences needs a reindexation
    for each separable subalgebra of `F`.  This was not written out.
  - *Additivity.*  A Cuntz sum uses invariant isometries in `A^α`, but its
    implementer needs central isometries that are not invariant.  This changes
    the cocycle.  Additivity on `M` was not checked.
