---
rg: 2
id: isolated-order-word-problems-are-bounded-by-positive-distortion
kind: claim
title: For a finitely presented group with a finitely generated positive cone, the word problem lies in NTIME ∩ coNTIME of a polynomial in the positive distortion and the Dehn function; so an isolated order can carry a hard word problem only through super-polynomial positive distortion or Dehn function, never through the regularity of its cone, and Higman-type bases carry no isolated order at all
distinct_from:
  finitely-generated-positive-cones-give-rigid-seeds: that puts every finitely generated positive cone into 𝒞 and poses (O); this bounds the word problems those groups can have and names the invariant a CAP counterexample must break.
---

**ESTABLISHED** for Theorem 1 and its corollaries (lane proof, bh-emitter-a, 2026-09-18; elementary; not
reviewed). Item 3 is cited; item 4 is open.

## Setting

`A = ⟨S | R⟩` is finitely presented, with a left order whose positive cone `P` is generated as a semigroup by a
finite set `S⁺`. Take `S = S⁺ ∪ (S⁺)^{-1}`, and let `δ` be the Dehn function.

The **positive distortion** is

    D_P(n) = max over g ≠ 1 with |g|_S ≤ n of  min{ |u| : u a word in S⁺, u = g or u = g^{-1} }.

It is finite, because `A = P ⊔ {1} ⊔ P^{-1}`. It is computable from `WP(A)`.

## Theorem 1

`WP(A) ∈ NTIME[q] ∩ coNTIME[q]` with `q(n) = poly(n + D_P(n) + δ(n + D_P(n)))`.

*Proof.* Let `w` have length `n`.
- **If `w = 1`:** a van Kampen diagram of area at most `δ(n)` certifies it, and it has size polynomial in the
  area.
- **If `w ≠ 1`:** guess a word `u` in `S⁺` with `|u| ≤ D_P(n)` and a sign `ε`, together with a van Kampen diagram
  for `w u^{−ε}` of area at most `δ(n + D_P(n))`.
  - Then `w = u^ε`, where `u` is a positive word. So `w ≠ 1`, because `1 ∉ P`.
- **Checking.** Both certificates are checked in polynomial time in their size. `∎`

## Corollaries

1. **Polynomial parameters.** If `D_P` and `δ` are polynomially bounded, then `WP(A) ∈ NP ∩ coNP`. If they are
   bounded by `2^{poly}`, then `WP(A) ∈ NEXP ∩ coNEXP`.
2. **The CAP test for this class.** Every such `A` lies in 𝒞 by `finitely-generated-positive-cones-give-rigid-seeds`.
   So a counterexample to CAP (with class EXP) among finitely presented groups with finitely generated positive
   cones must have `D_P` or `δ` of super-polynomial growth.
   - The machine must sit in the positive distortion or in the area. Large distortion alone certifies nothing,
     as the Baumslag–Gersten node shows. So this is a necessary condition, not a sufficient one.
3. **Regularity is not the invariant.** A finitely generated cone is automatically regular, as the image of the
   regular language `(S⁺)^+`. So regularity in the sense of Antolín–Rivas–Su (arXiv:2104.04475) holds for free
   and cannot force tameness. The quantity that could is `D_P`, together with a fellow-traveller property for
   positive words.
4. **Higman-type bases carry no isolated order.**
   - Free products of nontrivial groups have no isolated left orders (Rivas; as quoted in Ito, arXiv:1107.0545,
     §1, read 2026-09-18). Nor does `Z²`, nor does `F_2`.
   - So the base `Z² ∗ Z` of the Aanderaa–Cohen tower (see `seed-tower.md` and the tower nodes), and every free
     product stage of a Higman embedding, carry no finitely generated positive cone. A "machine among the cone
     generators" cannot be installed at those stages.
   - The only known isolation-preserving operation is Ito's partially central cyclic amalgamation, which
     transports complexity (`finitely-generated-positive-cones-give-rigid-seeds`).

## Where this leaves (O) and CAP

- **Attempted constructions.** None gives a hard example.
  - Dehornoy-style handle reduction on a hard group: an ordering with Ito's Property F would yield a
    handle-reduction word-problem algorithm. Its running time is controlled by `D_P` and `δ`, by Theorem 1.
  - Higman-style amalgams: blocked at the free-product stages, by item 4.
- **The tameness invariant, if CAP holds here.** The natural candidate is:

  **(O″)** Is `D_P` elementary, or even polynomial, for every finitely presented group with a finitely generated
  positive cone?

  - A yes, with elementary `δ`, puts all their word problems in ELEMENTARY.
  - A no is necessary for refuting CAP this way.
- **Recorded examples.** Braid groups (Dubrovina–Dubrovin), torus-knot groups and Ito amalgams all have small
  Dehn functions. We have not bounded `D_P` for them, so their `D_P` is a first computation to do.
- **Status.** (O) and (O″) are **open**.

## Lesson for general BH

A finitely generated positive cone certifies both answers of the word problem by short positive words, so all
its complexity is the positive distortion `D_P` plus the Dehn function.
- **What a machine would need.** A machine living in an isolated order must make positive words exponentially
  longer than the elements they represent.
- **Why the Higman base fails.** Its free-product stages admit no isolated order at all.
- **The one quantity to bound.** CAP on this class reduces to bounding `D_P`, and computing `D_P` on
  Dubrovina–Dubrovin braids is the first test.
