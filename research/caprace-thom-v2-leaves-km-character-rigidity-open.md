---
rg: 2
id: caprace-thom-v2-leaves-km-character-rigidity-open
kind: claim
title: Current Caprace-Thom proves Kac-Moody IRS rigidity, not character rigidity
distinct_from:
  simple-kazhdan-kac-moody-lattices-exist: that establishes finite presentation, simplicity and property T from Caprace-Remy; this audits a later and strictly stronger character claim.
  character-rigidity-equals-hyperfinite-hs-stability: that concerns consequences once character rigidity is available; this records that the cited current paper does not supply it.
artifacts:
  - notes/NONHYPERLINEAR_CHARACTER_REYNOLDS_INTEGRATION_2026-08-24.md
---

The current version of Caprace--Thom, arXiv:2606.27993v2, proves that the
specified compact-hyperbolic Kac--Moody lattices have exactly the two trivial
ergodic invariant random subgroups.  It does **not** prove that their
extremal characters are only regular and trivial.

The character-rigidity statement appeared in the superseded v1 abstract but
was removed in the completely rewritten v2.  Remark 5.4 of v2 says only that
absence of nontrivial characters seems plausible and identifies an unchecked
square-integrability condition needed for the proposed Creutz--Peterson
argument.  IRS rigidity cannot be substituted for classification of all
factor characters.

Primary source: P.-E. Caprace and A. Thom,
[*On the Howe--Moore property for automorphism groups of buildings*](https://arxiv.org/html/2606.27993v2),
Corollary 5.3 and Remark 5.4.

## Update (2026-09-13)

The missing conclusion is now established (unreviewed) at type `(2,4,6)`, `q >= 4`, by
`km-246-lattice-is-character-rigid`. This is not a direct substitution of IRS rigidity for the
classification of characters. IRS rigidity enters one step of the Creutz--Peterson argument. In
their Proposition 4.1(ii), the square-integrable lattice supplies finite stabilizers in the
non-factor case and an escaping element in the factor case. IRS rigidity of `S_q`, its
simplicity, and a Weyl element of infinite order do those jobs instead
(`irs-rigid-simple-dense-subgroups-act-properly-outer`). Caprace--Thom v1 had announced the
statement as its Theorem D, importing square-integrability from Remy's integrability theorem.
v2 withdrew it.
