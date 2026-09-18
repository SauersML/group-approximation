---
rg: 2
id: amenable-finite-cd-integral-group-rings-are-domains
kind: claim
title: The integral group ring of an amenable group of finite cohomological dimension has no zero divisors
distinct_from:
  kaplansky-zero-divisor-conjecture: that says k[G] has no zero divisors for every field k and every torsion-free group G; this is only the case k = Q (equivalently Z[G]) for amenable groups of finite cohomological dimension, and that conjecture implies it
  elementary-amenable-torsion-free-strong-atiyah: that is Linnell's established theorem for torsion-free elementary amenable groups, which gives domains only for them; this is the open statement for all amenable groups of finite cd, where elementary amenability is exactly what is unknown
  amenable-groups-of-finite-cd-are-virtually-solvable: that is Kropholler's question, which implies this statement (artifact Lemma 1.3); this is only its zero-divisor half, and in cohomological dimension 2 the two are equivalent
artifacts:
  - research/artifacts/kropholler-question-zero-divisor-split-2026-09-16.md
---

**OPEN.** Let `G` be an amenable group with `cd_Z G < ∞`. Then `Z[G]` has no zero divisors.
Equivalently, `Q[G]` has none (artifact, Remark 1.0).

This is the hypothesis that D. Degrijse (arXiv:1609.07635, Theorems A and B) adds to Kropholler's
question. Together with `amenable-finite-cd-domain-groups-are-virtually-solvable` it gives the root
`amenable-groups-of-finite-cd-are-virtually-solvable` (route
`kropholler-question-via-zero-divisor-split`).

**What is known.** Section numbers refer to the artifact.

- **Kaplansky implies it.** Kaplansky's zero-divisor conjecture over `Q` implies this statement,
  without using amenability (route `amenable-finite-cd-domains-via-kaplansky`). Groups of finite cd
  are torsion-free (artifact S1).
- **Elementary amenable groups.** It holds for elementary amenable `G`: such `G` is torsion-free,
  and `elementary-amenable-torsion-free-strong-atiyah` makes `C[G]` a domain.
- **The root implies it** (Lemma 1.3). That direction is not recorded as a route, which keeps the
  graph acyclic.
- **Finitely generated groups suffice.** It holds for all `G` if and only if it holds for finitely
  generated `G`, since a zero-divisor pair has finite support (Proposition 2.2).
- **Dimension 2.** For `cd G <= 2` it is equivalent to the root restricted to `cd G <= 2`: by
  Degrijse's Theorem B, domain group ring gives solvability, and Lemma 1.3 gives the converse
  (Section 1, "Dimension 2").
- **Linear groups.** It holds for linear `G`: Corollary 2.3 makes `G` virtually solvable, and
  Lemma 1.3 applies.

## Attempts

- **2026-09-16 (lane `hi-fron-amenable-groups-of-finite-cd-a`): split off from the root, not
  attacked directly.**
  - Every positive case this lane found needs elementary amenability, linearity, or the full
    Kaplansky conjecture. Elementary amenability and linearity are exactly what is unknown for the
    groups in question.
  - Using amenability does not help by itself. As far as this lane knows, the Ore-condition input
    for amenable groups (Tamari, cited by Degrijse) yields a division ring of fractions only once
    the group ring is known to be a domain. It does not exclude zero divisors.
  - No approach specific to finite cohomological dimension was found. Section 7 of the artifact
    records a filter on candidates (micro-supported actions), but it bears on the root, not on this
    claim.
- **2026-09-17 (lane `sw-112`, inverter): integral traces turn the zero-divisor half into a
  finiteness statement.**
  - `amenable-principal-fp-group-algebras-are-domains` (established): for torsion-free amenable
    `G`, `Q[G]` is a domain iff every principal left ideal `Q[G]a` is of type `FP`; with finite cd,
    `FP_∞` suffices, so left coherence of `Q[G]` suffices. Shape of a
    counterexample: a zero divisor `a` has `ann_l(a)` of `L²`-dimension `1 - dim NG a ∈ (0,1)`,
    and Baum--Connes (Higson--Kasparov) forbids such a module to have a finite resolution by
    finitely generated projectives. So `Q[G]a` is not of type `FP_∞`.
  - In dimension at most 2 this is an equivalence:
    `amenable-cd-two-solvable-iff-coherent-rational-group-algebra` (established) shows `G` solvable
    iff `Q[G]` left coherent iff `Z[G]` a domain. The open ring form is
    `amenable-cd-two-rational-group-algebras-are-coherent`.
  - Where it stops. In dimension `n >= 3` the criterion (principal ideals of type `FP_∞`) is
    equivalent to this claim, not strictly weaker; full coherence of `Q[G]` is sufficient but
    probably false for some solvable groups of finite cd, since it forces all finitely generated
    subgroups to be `FP_2` over `Q`.
- **2026-09-17 (lane `sw-112`, relaunch): the dimension-2 case needs only one homology group.**
  - `amenable-fp-iff-affiliated-top-homology-vanishes` (established) replaces the domain hypothesis
    in Degrijse's Theorem A with exact vanishing of `L²`-homology over the affiliated algebra
    `U(G)`. For amenable `G` of cd `n` and type `FP_{n-1}`, `G` is of type `FP` iff
    `H_{n-1}(G; U(G)) = 0`. The other degrees vanish automatically, by regularity of `U(G)` and
    dimension-flatness.
  - In dimension 2 this claim, for finitely generated `G`, is equivalent to `H_1(G; U(G)) = 0`,
    equivalently to type `FP_2`. Equivalently again: finitely many relators have a Fox Jacobian of
    von Neumann rank `d - 1`. So a counterexample is an amenable group of cd 2 where the increasing
    Fox ranks never attain their supremum `d - 1`.
