---
rg: 2
id: non-rf-relatively-hyperbolic-with-rf-peripherals
kind: claim
title: A relatively hyperbolic group that is not residually finite, with residually finite peripherals
distinct_from:
  oyakawa-graph-wreath-rf-iff-acting-group-rf: that settles residual finiteness inside Oyakawa's proper-cocompact hyperbolic family by discharging a published criterion; this asks for the existence of a relatively hyperbolic group with a specific pair of properties, and the one contact between them — Oyakawa's relative Theorem 1.3 as a possible source of such a group — is recorded as an open attack, not as an overlap of statements
  persistent-degree-two-class-on-hyperbolic-group: that is a cohomological statement about a group already known to be residually finite; this is a group-existence statement whose content is the peripheral structure, and neither implies the other
  non-residually-finite-hyperbolic-group: that asks for an ordinary word-hyperbolic group; this asks only for relative hyperbolicity but adds a condition on the peripheral subgroups, and by the filling route the two are equivalent in one direction — this claim implies that one, not conversely
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
---

Produce a group `G` that is hyperbolic relative to finitely many finitely
generated **residually finite** peripheral subgroups, such that `G` itself is
not residually finite.

## Why the peripheral condition is the whole content

Without it the claim is trivial and useless: any non-residually-finite
finitely generated group is hyperbolic relative to itself.  Relative
hyperbolicity is only a constraint together with a constraint on the
peripherals, and residual finiteness of the peripherals is exactly the
constraint that makes the filling route work — it is what lets every
peripheral be filled by a **finite-index** normal subgroup, so that the filled
group is hyperbolic relative to finite subgroups, i.e. word-hyperbolic.

By `non-rf-hyperbolic-via-relative-dehn-filling` this claim therefore implies
`non-residually-finite-hyperbolic-group`.  That is a warning, not an
encouragement: the relative problem is not a softer version of the hyperbolic
one, it is a repackaging, and any construction that looks like it produces
this is producing the hyperbolic counterexample.

## Attempts

- **Use a known non-sofic group.**  The unconditional non-sofic groups —
  Kun--Thom's wreath products (`kun-thom-nonsofic-wreath`),
  Fournier-Facio's torsion-free example, the binary Leavitt unit group — are
  not relatively hyperbolic with residually finite peripherals in any evident
  way.  Each carries an infinite lamp or defect subgroup that would have to be
  peripheral, and that subgroup is where the non-residual-finiteness lives, so
  it is precisely not residually finite.  This is structural, not accidental:
  the filling route says a residually finite peripheral cannot hide the
  witness.
- **Use the relatively hyperbolic Rips construction.**  Belegradek--Osin's
  relative version prescribes the peripherals of the output, which looks like
  the required control.  It dies the same way `non-rf-hyperbolic-via-rips-kernel`
  dies: the witness has to live in the kernel or in the quotient, and the
  construction does not let one prescribe the finite residual of either while
  keeping the peripheral list residually finite.
- **Deferred:** the honest position is that no attack here is independent of
  the attacks on the hyperbolic claim itself.  The node exists to hold the
  filling reduction, and to record that "relatively hyperbolic with nice
  peripherals" is not a weaker target.
