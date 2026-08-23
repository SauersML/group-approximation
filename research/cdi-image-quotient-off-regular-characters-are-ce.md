---
rg: 2
id: cdi-image-quotient-off-regular-characters-are-ce
kind: claim
title: The actual CDI image quotient has only CE factorial characters off the regular one
distinct_from:
  factor-universality-character-rigidity-implies-nonhyperlinear: that asks one fixed group to have both factor-representation universality and character rigidity; this asks only about the representation-dependent faithful image of one CDI envelope.
  character-rigid-signed-bcs-quotient: that seeks a character-rigid finite signed sector carrying a BCS quotient; this concerns the untwisted image quotient of the CDI factor representation.
  caprace-thom-v2-leaves-km-character-rigidity-open: that records an absent theorem for a proposed Kac--Moody source; this is the exact quotient-specific statement needed regardless of source family.
---

Fix a separable non-Connes-embeddable tracial algebra `M_0`, choose a CDI
factor representation

```text
pi:H -> U(Q),        pi(H)''=Q,        M_0 subset Q,
```

and put `Lambda=H/ker(pi)`.  Prove that every extremal character of
`Lambda` other than `delta_e` has a Connes-embeddable GNS factor.

This is deliberately about the *actual* kernel of the chosen universal
representation.  A rigidity theorem for `H`, for an unrelated quotient of
`H`, or for a separate Kac--Moody group does not establish it.  The CDI
construction presently supplies no control of `ker(pi)` that would identify
`Lambda` with a known character-rigid group.

## Attempts

- **Import rigidity through a chosen quotient of `H`.**  This stops because
  the chosen quotient map factors the CDI representation only when its
  kernel is contained in `ker(pi)`; universality gives no such containment.
- **Adjoin or induce from a known rigid group.**  Products and the relevant
  extensions retain proper infinite ICC quotient characters, while
  infinite-index induction has no canonical finite tracial amplification.
  The precise firewall is
  `standard-permanence-does-not-rigidify-the-cdi-image`.
- **Use a simple Kazhdan Kac--Moody group.**  It lies outside the CDI
  acylindrically hyperbolic source class, and the current Caprace--Thom
  theorem establishes IRS rigidity rather than the required character
  rigidity.  Direct CDI-style factor universality for such a group remains
  a genuinely new possible attack.
