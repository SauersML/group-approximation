---
rg: 2
id: kun-thom-wreath-stably-finite
kind: claim
title: Kaplansky stable finiteness for the Kun--Thom nonsofic wreath products
root: true
distinct_from:
  leavitt-group-algebra-not-stably-finite: that asks for an explicit one-sided inverse pair over `F_2` for the Leavitt unit group, a negative statement about the other nonsofic family; this is the positive statement for the wreath-product family, where no witness is being sought and the two known proof bridges are dead.
  exact-stably-finite-non-mf-reduced-group-algebra: that is a C-star statement about the reduced group C-star algebra of the sofic quotient witness, proved; this is algebraic stable finiteness of a group algebra over a field, open.
  kun-thom-nonsofic-wreath: that is the imported nonsoficity theorem about the same groups, established from Kun--Thom's preprint; this is a ring-theoretic question about their group algebras that nonsoficity leaves open and in fact is the reason the usual proof is unavailable.
artifacts:
  - research/artifacts/sofic-dividends-audit-2026-08-17.md
---

Let `W = (directSum_(G/Gamma) Z/2Z) semidirect G` be a Kun--Thom nonsofic
wreath product (`kun-thom-nonsofic-wreath`).  Is `k[W]` stably finite for
every field `k`?

*Marked `root` because it is a top-level dividend question, not a step in this
repository's programme: nothing else in this graph depends on it.  It is here
because `W` is one of the two families for which the sofic proof of stable
finiteness is unavailable by construction, and because the graph should record
which repairs have been tried.*

## What is already settled, and what the question really is

Characteristic zero is closed for **every** group
(`stable-finiteness-reduces-to-prime-field`), so nothing about `W` can be
learned there, and by the same node the remaining content is exactly stable
finiteness of `F_p[W]` for the prime fields.  Note the contrast with the
Leavitt lane: there the interesting possibility is that stable finiteness
*fails* (`leavitt-group-algebra-not-stably-finite`), and no failure is
conjectured here — `W` is amenable-by-residually-finite, so the expected
answer is yes and the difficulty is that no proof mechanism reaches it.

`W` sits in the extension `1 -> N -> W -> G -> 1` with `N` locally finite
(hence amenable) and `G` residually finite (hence sofic, hence `k[G]` stably
finite).  The sofic closure theorem runs the other way — sofic-by-amenable is
sofic — and `W` is the standing counterexample to any hope that the reverse
orientation is automatic.  So the question is precisely whether stable
finiteness lifts along a locally finite kernel.

## Attempts

Three approaches have been tried and all three are dead; each entry says where
it dies.

* **Modular radical.**  `k[W]/omega(k[N])k[W] = k[G]`, and direct finiteness
  descends modulo an ideal inside the Jacobson radical.  The lamp
  augmentation ideal is not inside it, in the lamp characteristic where it was
  most plausible: `modular-radical-does-not-lift-direct-finiteness`.
* **Soficity of the action.**  Away from the lamp characteristic `k[W]` is
  the algebraic crossed product of the locally constant functions on
  `{+1,-1}^(G/Gamma)` by the generalized Bernoulli action, and Kun--Thom's
  Corollary D says that action is not sofic.
* **Co-amenable transfer through the stabilizer,** the repair an external
  audit proposed on 2026-08-17, is blocked by property (T):
  `kun-thom-stabilizer-not-co-amenable`.

A fourth approach is deliberately *not* recorded as a route: "reduce to the
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
is supplied, the locally-finite-kernel route remains a gap rather than a
closure.

## What would count

A lifting theorem for locally finite kernels that does not go through the
Jacobson radical — equivalently, direct control of
`1 + M_n(omega(k[N])k[W])` — or an approximation mechanism that survives the
non-soficity of the generalized Bernoulli action.  Failing either, an
explicit one-sided inverse pair over `F_p[W]` would settle it the other way,
though nothing here suggests one exists.
