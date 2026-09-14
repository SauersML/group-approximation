---
rg: 2
id: non-surjunctive-group-with-stably-finite-group-algebras
kind: claim
title: Some group whose prime-field group algebras are all stably finite is not surjunctive
distinct_from:
  leavitt-unit-group-nonsurjunctive: that asks for a counterexample on one specific host by any mechanism, including the Kaplansky route; this asks for a counterexample on a host where the Kaplansky route is closed, so the automaton must be nonlinear in an essential way.
  gottschalk-surjunctivity-conjecture: that is the universal positive statement; this is a sharper negation that excludes counterexamples coming from one-sided inverses in group algebras.
artifacts:
  - research/artifacts/formal-polynomial-strict-pairs-2026-09-12.md
---

**OPEN.** There is a group `G` with `F_p[G]` stably finite for every prime `p`, and a finite alphabet,
carrying an injective cellular automaton that is not surjective.

**Why it is a separate target.** By `formal-polynomial-strict-pairs-need-unstable-linearization`, on
such a host every strict pair over an alphabet `F_q^n` is **non-formalizable**: no representatives of
the local rules make the left-inverse identity hold without `x^q = x`. No one-sided inverse in a group
algebra can witness it.

## Attempts

- **Formal designs.** Dead on such hosts: shears, triangular circuits, Nagata-type designs, and
  specializations of polynomial identities over infinite fields or `F_p[t]` are bijective (Theorem 1
  and Corollaries 2–3 of the artifact).
- **Where the collapse sits.** For `q = 2` with multilinear rules, `sigma o tau - id` has the form
  `sum_h (X_h^2 - X_h) P_h`, and the squares arise only at forward coincidences `g s m = g s' m'`.
  So the collapse terms live on the forward table, and the canonical table-group filters apply to
  them.
- **Decoder screen.** Dead: affine decoders, and decoders whose monomials multiply encoder outputs
  with pairwise disjoint essential footprints (`disjoint-footprint-decoders-force-kaplansky-failure`).
  A candidate needs a nonlinear decoder term at a forward coincidence read by both encoder copies.
- **The multilinear defect is not an invariant.** A sitewise reversible Toffoli pair has canonical
  defect `I + e_12` at a constant configuration on every group
  (`multilinear-collapse-defect-does-not-obstruct-bijectivity`). So forcing `D(c) = 0` cannot close
  this target. The representative-independent property is formalizability, and sitewise binary pairs
  are always formalizable (artifact, Section 6.2).
- **Binary-power alphabets.** `binary-left-inverse-pairs-are-formalizable` (open) would exclude
  every alphabet of size `2^n` on hosts with stably finite `F_2[G]`, through
  `stable-finiteness-forces-binary-surjunctivity`. A counterexample of this type over such an
  alphabet is exactly a non-formalizable strict pair.
- **Candidate hosts.** Main has nonsofic groups whose characteristic-two group algebras are stably
  finite (`kun-thom-binary-wreaths-stably-finite-in-characteristic-two`). Main also has permanence
  results making related Kun–Thom wreaths and doubles surjunctive
  (`kt-lef-graph-wreaths-surjunctive-and-nonsofic`, `kun-thom-group-doubles-are-surjunctive`), so a
  candidate host must lie outside their scope, and stable finiteness would still be needed at every
  odd prime.
- **Where it stops.** No non-formalizable strict pair is known on any group, and no non-formalizable
  bijective pair either (artifact, Section 6.4).
