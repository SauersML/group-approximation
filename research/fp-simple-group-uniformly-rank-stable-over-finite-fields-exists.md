---
rg: 2
id: fp-simple-group-uniformly-rank-stable-over-finite-fields-exists
kind: claim
title: Some finitely presented infinite simple group is uniformly rank-stable over finite fields
distinct_from:
  non-finite-field-linear-sofic-group-exists: that asks for any countable group outside finite-field linear soficity; this asks for a finitely presented simple one in stability form, where the Bauer--Blachar--Greenfeld algebra methods apply.
  binary-leavitt-unit-group-is-weakly-sofic: that is the open weak soficity of one explicit candidate; by fp-simple-group-not-linear-sofic-iff-rank-stable its failure is exactly this property for that candidate.
  fg-simple-weakly-sofic-groups-are-sofic: that is a rigidity statement for all finitely generated simple groups; this asks for one finitely presented simple group whose approximate representations over finite fields are all near the identity.
artifacts:
  - research/artifacts/solve-weakly-sofic-2026-09-13.md
---

**OPEN.** There are an infinite finitely presented simple group `G = <X | R>` and, for every `eps > 0`, a `delta > 0`
with the following property:
- take any finite field `F`, any `n`, and a tuple in `GL_n(F)^X` whose relators have normalized rank defect below
  `delta`;
- then some exact solution, in some `GL_(n')(F)`, `eps`-approximates it in padded rank.

By Lemma 0 of `fp-simple-not-linear-sofic-iff-rank-stable-proof` every exact solution is the identity. So equivalently:
every tuple with relator defects below `delta` has every generator within normalized rank `2 eps` of the identity.

**Payoff.** Glebsky--Rivera Conjecture 4.5, through `non-finite-field-linear-sofic-via-uniform-rank-stability`.

## Attempts

- **Candidates.** `R^x`, with `R = L_(F_2)(1,2)`, and Thompson's `V`. For these, the property is the negation of
  `binary-leavitt-unit-group-is-weakly-sofic` and of weak soficity of `V`.
- **Published permanence gives only residually finite groups.**
  - Bauer--Blachar--Greenfeld prove rank-stability for finite-dimensional algebras, free products, direct products and
    matrix rings. At the group level these operations reach free and direct products of finite groups, and such
    groups are residually finite, so never infinite and simple.
  - By their Proposition 2.2, a finitely presented rank-stable linear sofic algebra is residually finite-dimensional.
    So a candidate needs a stability proof that no permanence argument from residually finite pieces can supply.
  - No amalgam or HNN theorem exists (`atlas-rank-stability-literature-fence`).
  - See the artifact, Section 3.
- **Bachner's obstruction is silent here.** `free-quotient-obstructs-flexible-uniform-rank-stability` needs a free
  quotient, and a simple group has none.
- **What a proof must defeat.**
  - Every rank model mechanism recorded on `leavitt-el3-rank-models-over-finite-fields-are-trivial`, in every
    characteristic. The field varies, so odd characteristic counts too.
  - Every amenable quotient of `F_q[G]` of the kind in
    `fp-simple-group-algebra-amenable-quotient-gives-linear-soficity`.
