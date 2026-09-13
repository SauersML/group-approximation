---
rg: 2
id: binary-leavitt-unit-group-is-mif
kind: claim
title: The unit group of the Leavitt algebra L_(F_2)(1,n) is mixed-identity-free for every n >= 2
distinct_from:
  binary-leavitt-unit-group-satisfies-pbh: that is the permutational Boone--Higman property, established through an affine actor whose finite presentation is a separate theorem; this is MIF, which yields that property through BFFHZ Theorem C with no affine actor.
  binary-leavitt-unit-group-is-minimally-almost-periodic: that rules out finite-dimensional unitary representations; this rules out mixed identities.
  fp-simple-groups-embed-in-fp-simple-mif-groups: that is BFFHZ Question 3.4 for every finitely presented simple group; this settles the Leavitt instance that its Attempt 4 left undecided.
  linearly-transitive-groups-without-finite-rank-elements-are-mif: that is the abstract linear criterion; this verifies its hypotheses for the Cantor module of the Leavitt algebra.
---

**ESTABLISHED** through `binary-leavitt-unit-group-mif-proof`. Not independently reviewed;
no novelty is claimed.

For every `n >= 2` the group `U_n = L_(F_2)(1,n)^×` has no mixed identity. In particular
`U = U_2` is a finitely presented simple MIF group, by
`leavitt-unit-group-finitely-presented` and `binary-leavitt-unit-group-is-simple`.

**Mechanism.** `U_n` acts faithfully on the Cantor module `M = C({0..n-1}^N, F_2)`. This
action has two properties:
- the matrix units of depth `K` realize every linear automorphism of the functions of
  depth `K`, so every finite-dimensional partial isomorphism extends;
- simplicity of the algebra forces `g - 1` to have infinite rank for `g != 1`.

So `linearly-transitive-groups-without-finite-rank-elements-are-mif` applies.

## Consequences

- **Question 3.4 for `U`.** `U` is its own finitely presented simple MIF overgroup, so
  BFFHZ Question 3.4 holds for `U` trivially. BFFHZ Theorem E applies to `U` itself:
  `Aut_U(U * F_n)` (`n >= 2`) acts with type (A)
  (`relative-automorphism-of-fp-simple-mif-group-has-type-a-action`).
- **A second route to PBH.** Route `binary-leavitt-pbh-via-mif-envelope` gives
  `binary-leavitt-unit-group-satisfies-pbh` through Theorem C (iv) ⇒ (i). It does not
  use `leavitt-cantor-module-semidirect-product-is-fp`.
- **High transitivity is not claimed.** BFFHZ, Remark 3.5, arXiv:2503.21882v2 (extracted
  text on MSI, `bh-reviewer/2503.21882.txt` l.728–732): "for ﬁnitely generated simple
  groups, highly transitive implies MIF [HO16, Theorem 5.9] [LBMB22b, Proposition A.1],
  and in fact we are not aware of any ﬁnitely presented simple groups that are MIF but not
  highly transitive". No faithful highly transitive action of `U` is known to this graph
  (Attempt 1 on `binary-leavitt-unit-group-satisfies-pbh`). So whether `U` is such an
  example stays open.
- **The commutator test of Attempt 4.** On `fp-simple-groups-embed-in-fp-simple-mif-groups`,
  the characteristic-2 unipotent commutator `[1 + e, x(1 + e)x^-1]` is in particular not a
  mixed identity.

## Scope

- **Other finite fields.** Over `F_q` with `q > 2`, the unit group contains the central
  scalars `F_q^×`, so it is not MIF (`λ x λ^-1 x^-1` is a mixed identity). The criterion's
  scalar clause is exactly what fails. Quotients by scalars are not treated here.
- **Leavitt path algebras of other graphs.** Their depth-`K` matrix units form a direct sum
  of matrix algebras indexed by vertices, so condition (E) of the criterion needs a
  different verification. Not attempted.
