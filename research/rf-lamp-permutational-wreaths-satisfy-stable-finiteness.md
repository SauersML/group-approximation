---
rg: 2
id: rf-lamp-permutational-wreaths-satisfy-stable-finiteness
kind: claim
title: Permutational wreath products of residually finite groups satisfy Kaplansky over every field
distinct_from:
  kun-thom-binary-wreaths-stably-finite-in-characteristic-two: that treats binary lamps in characteristic two by augmentation separation; this permits arbitrary residually finite lamps and every coefficient characteristic by a different construction.
  residually-p-kernels-preserve-modular-stable-finiteness: that is a residual-prime extension theorem; this requires a permutation action but no matching between lamp torsion and coefficient characteristic.
  kun-thom-wreath-stably-finite: that is the concrete binary-lamp nonsofic-family target; this is the more general theorem for arbitrary residually finite lamp and base groups and arbitrary site actions.
---

Let A and G be residually finite groups, let X be any G-set, and let k
be any field. Then

    k[A wr_X G],    A wr_X G=(direct_sum_X A) semidirect G,

is stably finite. The action permutes the copies of A without applying
additional internal automorphisms. No finite-generation assumption on A,
G, or a stabilizer is required. No soficity of the action or of the wreath
product is assumed.

The proof constructs algebra homomorphisms

    Phi_r:k[A wr_X G] -> R^(tensor r),    r>=1,

whose kernels have zero intersection. The auxiliary algebra R retains
k[G] as a split quotient; its ideal is a direct sum of finite-support
matrix algebras over k[A x G_x]. Every finite tensor power of R is stably
finite by induction through those split extensions. A finite list of
marked sites detects any given nonzero group-algebra element, proving the
separation of the Phi_r without averaging or approximation.

In particular this proves the all-field claim `kun-thom-wreath-stably-finite`
for its residually finite-base family. It does not establish full
surjunctivity of those groups or Kaplansky's conjecture for arbitrary groups.

The exact induction hypotheses are isolated in
`wreath-finiteness-transfers-from-product-closed-classes`. This permits
iteration after the first wreath product has ceased to be residually
finite; `recursive-wreath-libraries-have-stably-finite-group-algebras`
records the resulting hierarchy and infinite-depth residual extension.

For actions with finite point stabilizers,
`rf-lamps-with-finite-stabilizers-preserve-direct-finiteness` removes the
residual-finiteness hypothesis on G: finiteness of k[G] at the relevant
matrix size suffices, and is also necessary. That theorem uses induced
finite-dimensional lamp representations whose errors relative to lamp
augmentation have finite rank. It includes all regular wreath products
but does not cover the arbitrary infinite stabilizers permitted here.
