---
rg: 2
id: sl2-q-in-permutational-boone-higman-class
kind: claim
title: SL_2(Q) lies in the permutational Boone--Higman class B_A, that is, the adelic complex of groups of SL_2(Q) has a type (A) envelope
distinct_from:
  gl-n-q-in-permutational-boone-higman-class: that is GL_n(Q) in B_A for every n >= 2, which implies this; this is its smallest case, SL_2(Q).
  sl2-q-embeds-in-fp-simple-group: that asks only for a finitely presented simple overgroup; this asks for the stronger type (A) envelope, which implies it by Zaremsky's Corollary B.
  adelic-median-graph-automorphisms-are-restricted-products: that rules out envelopes acting on the development of the adelic complex of groups; this is the envelope problem itself.
---

**OPEN.** There are a finitely presented group `Γ` with a type (A) action
(faithful, finitely generated point stabilizers, finitely many orbits of
two-element subsets) and an injective homomorphism `SL_2(Q) -> Γ`.

## The permanence form (gq critic pass 2, item 1)

`SL_2(Q)` is the fundamental group of the complex of groups over the
restricted product of chambers `∏'_p Δ_p`. Its vertex groups are
`Γ_c ≅ SL_2(Z)` and its edge groups are congruence subgroups of finite index
(`sl-n-q-is-colimit-of-lattice-stabilizers`). The vertex groups lie in `B_A`
(`fp-self-similar-subgroups-satisfy-permutational-boone-higman`, since `SL_2(Z)`
is a finitely generated linear group over `Q`). So this claim is exactly the
instance, for this complex of groups, of the permanence schema

> **(P)** if a group acts on `X = ∏'_p T_p` with vertex stabilizers in `B_A`
> and edge stabilizers of finite index in both endpoint stabilizers, then it
> lies in `B_A`.

(P) is not recorded as a claim. It includes every finitely generated group
acting freely on a finite product `∏_(p in S) T_p`: extend the action trivially
to the other factors, so that all stabilizers are trivial. `B_A` membership for
all of those is not known.

## Constraints on an envelope

- **Not cocompact.** The quotient is infinite: one vertex for each squarefree
  integer, and one edge for each vertex and each prime not dividing it
  (`cocompact-fg-stabilizer-actions-force-finite-generation`, item 3).
  No cocompact model with finitely generated stabilizers exists for
  `SL_2(Q)` at all (item 2 there). So no theorem whose inputs are cocompact
  actions with finitely presented stabilizers, such as Bux--Llosa Isenrich--Wu
  for locally finite trees, applies.
- **The development is no host.** No finitely generated group of automorphisms
  of `X` contains the standard `SL_2(Q)`. Any copy of `SL_2(Q)` in such a group
  sees only finitely many primes
  (`adelic-median-graph-automorphisms-are-restricted-products`). An envelope
  must mix the prime coordinates, as the prime shift `σ` of
  `gl-n-q-lies-in-prime-shift-permutation-group` does on `Q^n`.
- **Coherence.** The subcomplexes supported on a finite set `S` of primes have
  fundamental groups `SL_2(Z[1/S])`, and each is in `B_A`. So the claim is
  equivalent to finding one type (A) actor that contains the whole chain
  `SL_2(Z[1/S])` compatibly (the MT-C form, `research/artifacts/gq-gq-critic-2.md`).
- The constraints on hosts in `sl2-q-embeds-in-fp-simple-group` apply to `Γ` as
  well: O1 (no residually finite overgroup), O4 (no `VA`), no Q-free lifts, no
  natural piecewise-projective action, and no product of `PGL_2(K)`s.

## Attempts

1. **Envelope inside Aut(X), 2026-09-18 (gq-sl2q): dead.**
   `adelic-median-graph-automorphisms-are-restricted-products`, item 4.
2. **BLIW-type permanence, 2026-09-18 (gq-sl2q): the hypotheses cannot hold.**
   `cocompact-fg-stabilizer-actions-force-finite-generation`, item 2.
3. **Open direction.** An actor that contains `SL_2(Z)` and a prime-mixing
   element transporting the structure at `p` to that at `q`. Since
   `∂T_p ≅ P^1(Q_p)` are all Cantor sets, one candidate is a twisted
   Brin--Thompson-type group on `C^(primes)` whose actor contains a prime shift.
   Compare the prime-shift actor `K_n` and the open finite-presentation claim
   `prime-shift-affine-group-a1-is-finitely-presented`.
