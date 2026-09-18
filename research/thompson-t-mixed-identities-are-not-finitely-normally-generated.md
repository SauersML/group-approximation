---
rg: 2
id: thompson-t-mixed-identities-are-not-finitely-normally-generated
kind: claim
title: The mixed identities of Thompson's group T are not finitely normally generated in T * F_n for any n, answering BFFHZ Question 3.3 negatively
requires:
  - homeo-circle-three-arc-commutator-word-is-mixed-identity
  - bffhz-q33-is-normal-finite-generation-of-mixed-identities
distinct_from:
  bffhz-q33-is-normal-finite-generation-of-mixed-identities: that reformulates BFFHZ Question 3.3 and proves descent in the rank; this answers the question negatively, with Thompson's T as the counterexample.
  thompson-t-mixed-identity-problem-is-decidable: that shows the mixed identities of T form a recursive set; this shows they are not the normal closure of any finite subset, so the recursive set has no finite normal generating set.
  bffhz-q32-for-fp-simple-groups: that is Question 3.2, finite presentation of an automorphism-action image; it needs only a finite basis for substitution instances, which this result does not refute, so Question 3.2 for T stays open.
  homeo-circle-three-arc-commutator-word-is-mixed-identity: that writes down one mixed identity of T; this uses copies of it at every small scale to show no finite set of mixed identities normally generates them all.
artifacts:
  - research/artifacts/gq-bh-bh-bbmz-problems-status.md
---

**ESTABLISHED** by `thompson-t-mixed-identities-not-fng-proof` (lane proof, not
reviewed). Priority is unclear: no later answer to BFFHZ Question 3.3 was found
(bounded search, `research/artifacts/gq-bh-bh-lit-survey.md`), and no priority is
claimed until a proper literature check.

## The question

Belk--Fournier-Facio--Hyde--Zaremsky, arXiv:2503.21882v2, Question 3.3. The v2 HTML
was fetched on 2026-09-18, and quoted by the fetch as: "For G a finitely presented simple
group, is the quotient of G∗F_n by the Jacobson radical J_G(G∗F_n) finitely
presented? That is, is J_G(G∗F_n) finitely normally generated in G∗F_n?" By their
definition, which follows their Lemma 2.2, the mixed identities in `G∗F_n` make up
`J_G(G∗F_n)`.

## Statement

Let `T` be Thompson's group, acting on the circle and, through binary expansions, on
the Cantor set `C = {0,1}^N` as a subgroup of Thompson's `V`. Write `J_n(T)` for the
mixed identities of `T` in `T * F_n`, together with `1`.
1. **Small supports satisfy every mixed identity.** Let `w ∈ J_1(T)`. Then all
   points `u ∈ C` outside a finite set have a clopen neighbourhood `U` such that
   `w(P) = 1` for every homeomorphism `P` of `C` supported in `U`. In particular
   this holds for every `P ∈ V` supported in `U`.
2. **Some identity fails at every scale.** For every nonempty clopen `U ⊆ C` there
   are a mixed identity `w_U ∈ J_1(T)` (a three-arc word, with constants
   supported in `U`) and some `P ∈ V` supported in `U` with `w_U(P) ≠ 1`.
3. **Theorem.** For every `n >= 1`, `J_n(T)` is not the normal closure in `T * F_n`
   of any finite set. Equivalently, `(T * F_n)/J_T(T * F_n)` is not finitely
   presented. So Question 3.3 has a negative answer, and `T` is a counterexample.

## Why 1 and 2 give 3

Suppose `W ⊆ J_1(T)` is finite. Part 1 gives one clopen `U` that works for every `w`
in `W` at once: take the smallest of the neighbourhoods and avoid the union of the
exceptional sets. Take `w_U` and `P` from part 2. The homomorphism `T * Z -> V` that
is the inclusion on `T` and sends `x` to `P` kills `W`, but not `w_U`. So
`w_U ∉ ⟨⟨W⟩⟩`. For `n >= 2`, use descent: part 2 of
`bffhz-q33-is-normal-finite-generation-of-mixed-identities` says finite normal
generation at rank `n` implies it at rank 1.

## Scope

- **Not claimed: Question 3.2 for T.** Question 3.2 would force only a finite
  basis for substitution instances (`bffhz-q32-forces-finitely-based-mixed-identities`).
  Substitution instances `w(p(x))` are not supported in `U`, so part 1 does not
  apply to them. Whether `J_1(T)` is finitely based over overgroups is untouched.
- **Thompson's F.** The same proof works for `F` with the interval version of the
  three-arc word, since part 1 never uses simplicity. But `F` is not simple, so it
  is not an instance of Question 3.3.
- **General mechanism.** Take a group `G` of homeomorphisms of a space `X` with an
  overgroup `H` acting on the same space. Suppose that:
  - elements of `G` have only finitely many fixed points at which they are not locally the identity;
  - `G` has infinite-order elements supported in every small neighbourhood;
  - `H` violates some `G`-mixed identity with constants supported in every open set.

  Then `J_1(G)` is not finitely normally generated. For `T`, the overgroup `V`
  breaks the circle's cyclic order at every scale.
