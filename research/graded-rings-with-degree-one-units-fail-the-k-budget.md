---
rg: 2
id: graded-rings-with-degree-one-units-fail-the-k-budget
kind: claim
title: A ring containing Q with a Z-grading that has a unit in degree one is a skew Laurent ring over its degree-zero part, so either its rational scalars are almost all killed in K_1 or no E_N is finitely presented; this covers ring lamplighters and Baumslag-type extensions of them
distinct_from:
  laurent-rational-symbols-block-fp-elementary-groups: that assumes R = B[u^±;σ] is given together with a base B whose K_1 detects Q^x; this recognizes the skew Laurent structure from any grading with a degree-one unit, and derives the base condition from K_1 of R, so the test can be read off a presentation.
  matrix-corner-laurent-rings-block-fp-elementary-groups: that treats crossed products over odometer factors with an indicable subgroup; this treats every Z-graded ring with a degree-one unit, with no dynamics.
  fp-simple-resolvent-ring-with-divisible-unit-class: that is the ring gate; this rules out one design shape for it, the ring lamplighter and its graded Baumslag-type cures.
---

**ESTABLISHED** through `graded-rings-with-degree-one-units-fail-the-k-budget-proof`. Refereed:
gq-referee-a PASS, proof-gap lens (report 223c763b9, W1 and nits applied); gq-referee-b PASS, citation and scope lens
(report e39e24bdb). Elementary given `laurent-rational-symbols-block-fp-elementary-groups`. No priority is claimed.

**Statement.** Let `R` be a unital ring with a unital map `Q -> R`, and let `R = ⊕_(k in Z) R_k` be a grading
(`R_i R_j ⊆ R_(i+j)`) with a unit `u in R_1`.
1. **Structure.** `u^-1 in R_(-1)`, `Q ⊆ R_0`, `R_k = R_0 u^k`, and `R = R_0[u, u^-1; σ]` with
   `σ = (b -> u b u^-1)`, an automorphism of `R_0` fixing `Q`.
2. **Dichotomy.** Exactly one of the following holds.
   - The image of `Q^x -> K_1(R)` is finitely generated. Then `ker(Q^x -> K_1(R))` is not finitely generated,
     so the `K_1` half of the K-budget fails (`rational-k1-detection-forces-infinite-order-unit-class`).
   - It is not. Then the symbols `{λ, u}`, `λ in Q^x`, generate an infinitely generated subgroup of `K_2(R)`,
     and `E_N(R)` is not finitely presented for any `N >= 3`, nor is `E_N(R)/C` for a finite normal `C`.

## Consequences

- **The ring lamplighter.** `U_n ⋊_α Z`, with `U_n = ⊗_(k in Z) M_n(Q)` (algebraic tensor product) and `α` the
  shift, is graded by the power of the implementing unit. It is in the second case: `Q^x -> K_1(U_n)` has finite kernel
  (`{±1}` for `n` even, `{1}` for `n` odd). So no `E_N(U_n ⋊ Z)` is finitely presented. The same holds for
  `U_Q ⋊ Z`, with kernel `{±1}`. Adding homogeneous relations keeps the ring under the dichotomy, but it changes
  `R_0` and can kill rational `K_1` classes, moving the ring to the first case (gq-referee-a, W1). This is independent of the infinitely many commutation relations
  `[A_0, u^k A_0 u^-k] = 0` that also block finite presentation of the ring.
- **Graded cures are dead.** Suppose extra generators and relations are added, as in Baumslag's embedding of
  `Z/p ≀ Z` into a finitely presented metabelian group: a generator `y` with `y u = u y` and
  `y a y^-1 = a · u a u^-1` for the generators `a` of `A_0`. These relations are homogeneous when `y` has degree `0` and `u` degree `1`, and `u`
  stays a unit. So the result falls under the dichotomy. A cure must break every such grading: make the shift a
  non-unit, as with the isometries of a Cuntz--Pimsner ring, or use inhomogeneous relations.
- **Pimsner calibration.** For a skew Laurent ring, `[X] = σ_*` fixes every rational class `[λ] in K_1(R_0)`,
  because `σ` fixes `Q`. So those classes lie in `ker(1 - σ_*)` and lift to the symbols `{λ, u}`. This is what
  forces the constraint "`1 - [X]` injective on the rational part of `K_1` of the base" in Pimsner-type designs,
  through item 5 of the gate as extended to all symbols `{λ, x}` (`resolvent-register-units-give-rational-symbols`).
  It is not forced by `K_1` detection. The ring lamplighter has `[X] = id` on `K_0(U_n) = Z[1/n]`, and `[1]` of
  infinite order; it fails through `K_2`, not through `K_0`.
- **Not decided.** Whether `U_n ⋊ Z` embeds in a finitely presented ring whose `[1]` has infinite order. The
  dichotomy only constrains rings that keep a grading with a degree-one unit.
