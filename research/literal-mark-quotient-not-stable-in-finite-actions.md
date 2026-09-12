---
rg: 2
id: literal-mark-quotient-not-stable-in-finite-actions
kind: claim
title: The literal marked quotient is sofic but not stable in permutations
distinct_from:
  literal-group-not-stable-in-finite-actions: That is the same conclusion for `E` itself, obtained from non-residual-finiteness of `E`; this one is for the central quotient `E/<w>` and uses the exact finite residual of that quotient.
  literal-mark-quotient-flexibly-stable: That claim asserts flexible stability of `E/<w>`; this one refutes it, since flexible stability implies stability in finite actions.
  literal-mark-quotient-finite-residual: That computes which elements survive finite quotients; this draws the permutation-stability consequence from the fact that some do not.
  literal-mark-quotient-sofic: That is soficity of `E/<w>`; this combines it with non-residual-finiteness.
  sofic-stable-implies-residually-finite: That is the general principle, quantified over all countable groups; this applies it to one explicit group whose soficity and nontrivial finite residual are both computed in this repository.
artifacts:
  - notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md
  - notes/SOFIC_STABLE_IMPLIES_RESIDUALLY_FINITE_2026-08-14.md
---

`E/<w> = (*_{i in I} (Z/2)^8) semidirect V` is **not stable in finite actions**
(Gohla--Thom Definition 3.7), hence not stable in any stronger permutation
sense.  In particular `literal-mark-quotient-flexibly-stable` is FALSE.

*Trust surface, split by conclusion.*  "Not stable in finite actions" is
internal end to end.  The strengthening to any stronger notion, which is what
refutes the flexible-stability claim, uses Gohla--Thom Lemma 3.6 — external,
source-verified, recorded in `gohla-thom-stable-base-nonsofic-extension`.

Both inputs are now in-repo: `E/<w>` is sofic
(`literal-mark-quotient-sofic`), and it is not residually finite, because
`literal-mark-quotient-finite-residual` computes its finite residual to be the
nontrivial level-collapse kernel `R` — which even contains elements of infinite
order.  A sofic group stable in finite actions is residually finite
(`sofic-stable-implies-residually-finite`).

Consequence for the Gohla--Thom line: hypothesis (i) of their Theorem 3.13
fails outright for `E/<w>`, so that theorem never applied to the pair
`(E/<w>, E)` and says nothing here about the cosystolic inequality.  The
three-way disjunction previously recorded is resolved, and it is resolved on
the residual-finiteness disjunct.  The stability conclusion above is
independent of it.
