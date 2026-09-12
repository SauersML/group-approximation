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
  - research/artifacts/z3-normal-rotation-and-eigen-hyperplane-rigidity-2026-09-12.md
---

**OPEN.** There is a group `G` with `F_p[G]` stably finite for every prime `p`, and a finite alphabet,
carrying an injective cellular automaton that is not surjective.

**Why it is a separate target.** By `formal-polynomial-strict-pairs-need-unstable-linearization`, on
such a host every strict pair over an alphabet `F_q^n` is **non-formalizable**, even after adding
identity ancilla tracks, since `tau x id` is strict iff `tau` is. No representatives of
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
- **Binary-power alphabets** (corrected by w3-nonformal).
  - Plain formalizability is refuted (`binary-left-inverse-pairs-need-not-be-formalizable`).
  - The live exclusions are stable and virtual: `injective-binary-automata-are-stably-formalizable`
    and `injective-automata-over-fg-groups-are-virtually-formalizable`, both open. Each gives
    `stable-finiteness-forces-binary-surjunctivity`.
  - So a counterexample over an alphabet of size `2^n` on such a host must be an injective,
    non-surjective automaton `tau` with two properties:
    - for no `m` does `tau x id_m` have a left inverse forming a formalizable pair;
    - no left inverse formalizes after regrouping along a finite-index subgroup of the memory group.
- **One-track rigidity does not feed this target** (w3-nonformal).
  - The `Z_3` obstructions concern one track: `z3-level-preserving-automorphisms-rotate-uniformly`,
    `z3-equivariant-automorphisms-have-constant-normal-rotation`,
    `z3-eigen-hyperplane-stabilizer-is-the-triangular-group`, and the open test
    `z3-weight-one-rotation-is-not-an-automorphism-shadow`.
  - With a second track, `(s, v_1 + s v_2, v_2)` is an equivariant automorphism with a non-uniform
    shadow. Its normal derivative along the fixed plane has determinant 1. So neither the cone nor the
    normal rotation survives stabilization.
  - A decoder that needs a non-formalizable local rule must therefore be obstructed by an invariant
    that survives identity tracks and regrouping.
  - `marker-involution-over-rationals-is-not-virtually-formalizable` does not bear on this: it is
    bijective, and the Kaplansky payoff localizes to the finitely generated memory subgroup.
- **Candidate hosts.** Main has nonsofic groups whose characteristic-two group algebras are stably
  finite (`kun-thom-binary-wreaths-stably-finite-in-characteristic-two`). Main also has permanence
  results making related Kun–Thom wreaths and doubles surjunctive
  (`kt-lef-graph-wreaths-surjunctive-and-nonsofic`, `kun-thom-group-doubles-are-surjunctive`), so a
  candidate host must lie outside their scope, and stable finiteness would still be needed at every
  odd prime.
- **Where it stops.** No non-formalizable strict pair is known on any group, and no non-formalizable
  bijective pair either (artifact, Section 6.4).
