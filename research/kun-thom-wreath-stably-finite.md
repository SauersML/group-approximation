---
rg: 2
id: kun-thom-wreath-stably-finite
kind: claim
title: Kaplansky stable finiteness for the Kun--Thom nonsofic wreath products
root: true
distinct_from:
  leavitt-group-algebra-not-stably-finite: that asks for an explicit one-sided inverse pair over F_2 for the Leavitt unit group; this asks for finiteness of the wreath family, now proved in characteristic two but open in odd positive characteristics.
  exact-stably-finite-non-mf-reduced-group-algebra: that is a C-star statement about the reduced group C-star algebra of the sofic quotient witness, proved; this is algebraic stable finiteness of a group algebra over a field, open.
  kun-thom-nonsofic-wreath: that is the imported nonsoficity theorem about the same groups, established from Kun--Thom's preprint; this is a ring-theoretic question about their group algebras that nonsoficity leaves open and in fact is the reason the usual proof is unavailable.
artifacts:
  - research/artifacts/sofic-dividends-audit-2026-08-17.md
---

Let `W = (directSum_(G/Gamma) Z/2Z) semidirect G` be a Kun--Thom nonsofic
wreath product with G residually finite (`kun-thom-nonsofic-wreath`,
including its explicit Theorem E family). Is `k[W]` stably finite for
every field `k`?

*Marked `root` because it is a top-level dividend question, not a step in this
repository's programme: nothing else in this graph depends on it.  It is here
because `W` is one of the two families for which the sofic proof of stable
finiteness is unavailable by construction, and because the graph should record
which repairs have been tried.*

## What is already settled, and what the question really is

Characteristic zero is closed for **every** group
(`stable-finiteness-reduces-to-prime-field`). Characteristic two is now
closed by `kun-thom-binary-wreaths-stably-finite-in-characteristic-two`,
for every characteristic-two field. The remaining content is stable
finiteness of `F_p[W]` for odd primes p. Note the contrast with the
Leavitt lane: there the interesting possibility is that stable finiteness
*fails* (`leavitt-group-algebra-not-stably-finite`), and no failure is
conjectured here — `W` is amenable-by-residually-finite, so the expected
answer is yes; the remaining difficulty is in odd positive characteristics.

`W` sits in the extension `1 -> N -> W -> G -> 1` with `N` locally finite
(hence amenable) and `G` residually finite (hence sofic, hence `k[G]` stably
finite).  The sofic closure theorem runs the other way — sofic-by-amenable is
sofic — and `W` is the standing counterexample to any hope that the reverse
orientation is automatic. In characteristic two, stable finiteness does
lift here: N is residually a finite two-group, and
`residually-p-kernels-preserve-modular-stable-finiteness` applies. This
does not settle locally finite kernels in other coefficient characteristics.

## Attempts

Three earlier approaches were audited. The first obstruction remains true
but has now been bypassed by a different ring-theoretic argument.

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

A bare reduction is deliberately *not* recorded as a route: "reduce to the
prime fields and prove it there" would be a restatement dressed as a
reduction, because by `stable-finiteness-reduces-to-prime-field` the
prime-field statement is *equivalent* to this one, so it renames the problem
instead of reducing it.


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
than a closure. The established characteristic-two argument uses the
specific residual-two property of N and makes no use of that preprint.

## What would count

For odd primes, a proof must control inverse defects in the nonmodular lamp
crossed product, or provide another finiteness mechanism. The modular
separation argument does not apply: binary lamp idempotents in odd
characteristic already make the augmentation powers nonseparated.
An explicit one-sided inverse pair over F_p[W], p odd, would instead
refute this all-field claim. Neither outcome is currently established.
