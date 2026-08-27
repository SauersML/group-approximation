---
rg: 2
id: elementary-amenable-strong-atiyah-citation
kind: route
title: Read Fisher-Ng 2606.19606 section 1.1 for the known Strong Atiyah classes
target: elementary-amenable-torsion-free-strong-atiyah
requires: []
artifacts:
  - research/artifacts/strong-atiyah-audit-2026-08-17.md
---

Literature import.  Direct reading of arXiv:2606.19606 (Sam P. Fisher and
Andrew Ng, *Outer automorphism groups and the Atiyah Conjecture*, June 2026),
Section 1.1, on 2026-08-17.

Quoted: the Strong Atiyah Conjecture over `C` is *"known for many classes of
groups, including all locally indicable groups [30], braid groups [42],
**elementary amenable groups** [41], virtually compact special groups [56],
and 3-manifold groups [19, 35]"*, reference [41] being Linnell.

Read in the same pass, and recorded on the target root
`strong-atiyah-torsion-free` rather than here:

* Linnell's equivalence -- *"For `K ⊆ C`, Linnell showed that the Strong
  Atiyah Conjecture over `K` for a torsion-free group `G` is equivalent to the
  division closure of `K[G]` in its algebra of affiliated operators being a
  division ring [41]."*
* the open status -- the question *"has been reformulated into the following
  open problem known as the Strong Atiyah Conjecture"* (their Conjecture 1.1,
  stated with `rk in (1/lcm(G))Z` for groups with a bound on the orders of
  finite subgroups; torsion-free gives `lcm = 1`).
* Kaplansky -- *"if `G` is torsion-free and satisfies the Strong Atiyah
  Conjecture over `K`, then the group algebra `K[G]` is a domain."*
* and, bearing on the `L^2`-Betti route, that known constructions *"yielding
  irrational `L^2`-Betti numbers all have torsion subgroups of unbounded
  order."*

Trust surface: this is a `requires: []` import at **survey-pinpoint** level.
The sentence naming elementary amenable groups was read from the source;
Linnell's original paper was not.  That suffices for the single use made of
it -- certifying that one concrete solvable group's Linnell closure is a
division ring -- but a route needing the theorem's hypotheses in detail must
read Linnell first.
