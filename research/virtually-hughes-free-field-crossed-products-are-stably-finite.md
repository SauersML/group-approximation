---
rg: 2
id: virtually-hughes-free-field-crossed-products-are-stably-finite
kind: claim
title: A field crossed product is stably finite, hence has the rank condition, when every finitely generated subgroup is virtually residually torsion-free nilpotent, free-by-cyclic or locally indicable amenable; for faithful actions the rank condition equals stable finiteness
distinct_from:
  field-crossed-product-rank-condition-survival-cases: that gives the rank condition through an amenable twist, algebraic coefficients or an invariant complex measure; this uses finite-index Hughes-free division rings, needs no measure and no amenability, and covers the Möbius case Q(x) ⋊ PSL_2(Z) that evades all three regimes there.
  fsp-graph-of-rings-and-linnell-extension-imports: that imports division rings for crossed products over locally indicable groups; this transfers them to finite-index overgroups with torsion and to arbitrary groups by locality, and adds the simplicity reduction for field crossed products.
  some-field-crossed-product-fails-the-rank-condition: that is the open existence of a witness; this rules out the whole ordered and indicable class of witnesses and shows the class stops at Kazhdan subgroups.
  rank-condition-rings-have-weakly-finite-images: that is the general ring equivalence; this specializes it to simple field crossed products, where the only image is the ring itself.
artifacts:
  - research/artifacts/field-crossed-product-virtual-division-embedding-2026-09-17.md
---

Let `R = K*G` be a crossed product over a commutative field `K`, with any action `σ` and 2-cocycle `α`.

1. **Simplicity.** If `σ` is faithful, `R` is simple. So `R` has the rank condition iff it is stably finite.
2. **Locality and finite index.** `R` is stably finite iff `K*H` is for every finitely generated `H <= G`. If
   `N <= G` has finite index `n` and `K*N` embeds in a stably finite ring `S`, then `R` embeds in `M_n(S)`.
3. **Theorem.** Suppose every finitely generated `H <= G` has a finite-index subgroup that is residually
   torsion-free nilpotent (e.g. free, or a subgroup of a RAAG), locally indicable amenable, free-by-cyclic, or a
   finite graph of locally indicable groups with such vertex groups. Then `R` is stably finite and has the
   rank condition.
4. **Consequence.** `Q(x) ⋊ PSL_2(Z)` by Möbius substitutions, and every `K*G` with `G` virtually free, has the
   rank condition. This is the lead test case of `some-field-crossed-product-fails-the-rank-condition`. The
   deduction uses one classical input, that `PSL_2(Z)` is virtually free, which is not a graph import.
5. **Boundary.** An infinite finitely generated Kazhdan group has no locally indicable finite-index subgroup, so
   item 3 says nothing on any group containing one. A rank-condition witness, and so a profile-level kill of
   Bernoulli maximality via `twisted-linear-profile-deficits-are-rank-condition-failures`, has to contain a
   finitely generated subgroup outside the virtual Hughes-free class, e.g. a Kazhdan subgroup.

**ESTABLISHED 2026-09-17** by [[virtually-hughes-free-field-crossed-products-proof]] (items 1–3 and 5; item 4
adds the classical input above). Not independently reviewed; no priority claimed.
