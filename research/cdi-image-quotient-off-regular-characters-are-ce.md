---
rg: 2
id: cdi-image-quotient-off-regular-characters-are-ce
kind: claim
title: The actual CDI image quotient has only CE faithful factorial characters off the regular one
distinct_from:
  factor-universality-character-rigidity-implies-nonhyperlinear: that asks one fixed group to have both factor-representation universality and character rigidity; this asks only about the representation-dependent faithful image of one CDI envelope.
  character-rigid-signed-bcs-quotient: that seeks a character-rigid finite signed sector carrying a BCS quotient; this concerns the untwisted image quotient of the CDI factor representation.
  caprace-thom-v2-leaves-km-character-rigidity-open: that records an absent theorem for a proposed Kac--Moody source; this is the exact quotient-specific statement needed regardless of source family.
  cdi-image-central-wreath-retains-the-regularity-gate: that computes the actual image and shows its distinguished character is regular exactly when the input image character already is; this asks for classification of all other factorial characters after a special choice has somehow crossed that gate.
---

Fix a separable non-Connes-embeddable tracial algebra `M_0`, choose a CDI
factor representation

```text
pi:H -> U(Q),        pi(H)''=Q,        M_0 subset Q,
```

and put `Lambda=H/ker(pi)`.  Prove only the following faithful-character
statement:

```text
every faithful extremal character of Lambda other than delta_e
has a Connes-embeddable GNS factor.                         (CIF1)
```

This is strictly weaker than classifying every nonregular factorial
character.  The distinguished character

```text
chi(g)=tau_Q(pi_bar(g))
```

is faithful: if `chi(g)=1`, faithfulness of the trace gives
`pi_bar(g)=1`, and injectivity of `pi_bar` gives `g=e`.  It is extremal and
its GNS factor is the non-CE factor `Q`.  Hence `(CIF1)` forces `chi` to be
`delta_e`, identifies `Q` trace-preservingly with `L(Lambda)`, and makes
`Lambda` nonhyperlinear.

The weakening removes the structural obstruction in
`ah-groups-fail-regular-fd-character-rigidity`: the proper-quotient
characters constructed there all have nontrivial kernel, so none refutes
`(CIF1)`.  Thus the exact high-cascade target is faithful factor-character
rigidity of the actual CDI image, not rigidity of its entire character
simplex.

Even this weaker statement cannot hold for an arbitrary CDI choice.  By
`cdi-image-central-wreath-retains-the-regularity-gate`, the distinguished
factor character of `Lambda` is itself non-CE and is regular exactly when
the input image character is regular.  The standard allowed Ge--Popa
generator choice has an intermediate coefficient; after dividing by the
kernel, its distinguished character is a faithful nonregular non-CE
character, so its actual image quotient is a counterexample to `(CIF1)`.
The claim must therefore be read existentially: construct a special CDI
choice for which `(CIF1)` holds.  Applying it to the distinguished character
forces the input image character to be regular, so this route does not
inherit a shortcut from the published construction.

This is deliberately about the *actual* kernel of the chosen universal
representation.  A rigidity theorem for `H`, for an unrelated quotient of
`H`, or for a separate Kac--Moody group does not establish it.  The CDI
construction presently supplies no control of `ker(pi)` that would identify
`Lambda` with a known character-rigid group.

## Attempts

- **Use the intrinsic wreath-like image structure.**  The exact quotient is
  a central wreath extension with base `(Gamma/S)^(B)`, where
  `Gamma=pi_0(F_3)` and `S=Gamma intersect T1`.  This normal form preserves
  the input regularity gate and gives no character collapse.  For the
  standard generator choice it instead transports an explicit nonregular
  faithful nonregular non-CE character.

- **Import rigidity through a chosen quotient of `H`.**  This stops because
  the chosen quotient map factors the CDI representation only when its
  kernel is contained in `ker(pi)`; universality gives no such containment.
- **Adjoin or induce from a known rigid group.**  Products and the relevant
  extensions retain proper infinite ICC quotient characters, while
  infinite-index induction has no canonical finite tracial amplification.
  The precise firewall is
  `standard-permanence-does-not-rigidify-the-cdi-image`.
- **Use acylindrical-hyperbolic quotient characters as a no-go.**  They do
  refute regular-or-finite-dimensional rigidity of the source group, but
  they are nonfaithful and therefore do not refute `(CIF1)`.  The faithful
  restriction is the surviving classification problem.
- **Use a simple Kazhdan Kac--Moody group.**  It lies outside the CDI
  acylindrically hyperbolic source class, and the current Caprace--Thom
  theorem establishes IRS rigidity rather than the required character
  rigidity.  Direct CDI-style factor universality for such a group remains
  a genuinely new possible attack.
