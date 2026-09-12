---
rg: 2
id: kun-thom-wreath-stably-finite
kind: claim
title: Kaplansky stable finiteness for the Kun--Thom nonsofic wreath products
root: true
distinct_from:
  leavitt-group-algebra-not-stably-finite: that asks for an inverse defect for the Leavitt unit group; this proves stable finiteness for the residually finite-base wreath family over every field.
  exact-stably-finite-non-mf-reduced-group-algebra: that concerns a reduced C-star algebra; this concerns ordinary group algebras over every field, including positive characteristic.
  kun-thom-nonsofic-wreath: that supplies nonsoficity of the named groups; the finiteness proof here instead uses the general residually finite lamp and base theorem, independently of nonsoficity.
artifacts:
  - research/artifacts/sofic-dividends-audit-2026-08-17.md
---

Let `W = (directSum_(G/Gamma) Z/2Z) semidirect G` be a Kun--Thom nonsofic
wreath product with G residually finite (`kun-thom-nonsofic-wreath`,
including its explicit Theorem E family). Then `k[W]` is stably finite for
every field `k`.

*Marked `root` because it is a top-level dividend question, not a step in this
repository's programme: nothing else in this graph depends on it.  It is here
because `W` is one of the two families for which the sofic proof of stable
finiteness is unavailable by construction, and because the graph should record
which repairs have been tried.*

## All-field proof

`rf-lamp-permutational-wreaths-satisfy-stable-finiteness` proves that
k[A wr_X G] is stably finite whenever A and G are residually finite,
for any G-set X and any field k. Apply it with A=C_2 and X=G/Gamma.
The route `kun-thom-all-fields-from-finite-particle-lamps` records this
specialization. In particular the previously open odd-characteristic cases
are now established by the same proof.

The proof detects a finite-support group-algebra element by a finite list
of marked lamp sites. These tests take values in tensor powers of an
auxiliary algebra with split quotient k[G] and a local-matrix ideal over
stabilizer group algebras. The tensor powers are stably finite by a
strengthened induction through split extensions. Their tests jointly
separate every nonzero inverse defect. No finite approximation of the
generalized Bernoulli action is used.

The independent proof in
`kun-thom-binary-wreaths-stably-finite-in-characteristic-two` remains valid:
the modular lamp augmentation ideal has separated powers, which exclude
nonzero idempotent inverse defects. The new proof removes the coefficient-
characteristic restriction without claiming the nonmodular powers are
separated.

## Attempts

Three earlier approaches were audited. Their restricted obstructions remain
valid, but none obstructs the all-field proof above.

* **Modular radical.** The lamp augmentation ideal need not lie in the
  Jacobson radical (`modular-radical-does-not-lift-direct-finiteness`).
  Nevertheless its powers have zero intersection in characteristic two.
  Any inverse defect is an idempotent in this ideal, hence belongs to every
  power and is zero. This establishes the modular case without inverting
  every element of one plus the ideal.
* **Soficity of the action.**  Away from the lamp characteristic `k[W]` is
  the algebraic crossed product of the locally constant functions on
  `{+1,-1}^(G/Gamma)` by the generalized Bernoulli action, and Kun--Thom's
  Corollary D says that action is not sofic.
* **Co-amenable transfer through the stabilizer,** the repair an external
  audit proposed on 2026-08-17, is blocked by property (T):
  `kun-thom-stabilizer-not-co-amenable`.

## Citation firewall: the locally-finite-kernel shortcut is not established here

There is a tempting apparent closure in M. Shahryari's withdrawn preprint
*“A note on surjunctive groups”* (arXiv:2002.05352), whose abstract states that
a semidirect product of a locally finite group by a surjunctive group is
surjunctive.  Do **not** use that abstract as a proof of this node.  The
peer-reviewed Arzhantseva--Gal theorem cited in that circle of ideas proves the
semidirect-extension statement for a **finitely generated residually finite**
kernel.  The lamp kernel

    N = directSum_(G/Gamma) Z/2Z

is locally finite but, in the Kun--Thom examples of interest, infinite and not
finitely generated.  Thus the published theorem does not apply.  Until the
withdrawn argument is independently reconstructed or another extension theorem
is supplied, the general locally-finite-kernel route remains a gap rather
than a closure in that generality. Both proofs here use the particular
structure of the kernel or its permutation action, and make no use of
that preprint. Stable finiteness is not being inferred from its stronger
surjunctivity assertion.

## Scope

This settles the all-field group-algebra question for the stated family.
It does not prove full nonlinear surjunctivity of W, direct finiteness
for the Leavitt unit group, or Kaplansky's conjecture for arbitrary groups.
