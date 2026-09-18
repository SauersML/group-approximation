---
rg: 2
id: amenable-cd-two-rational-group-algebras-are-coherent
kind: claim
title: The rational group algebra of an amenable group of cohomological dimension 2 is left coherent (Kropholler's question in dimension 2, ring form)
distinct_from:
  amenable-cd-two-solvable-iff-coherent-rational-group-algebra: that is the established equivalence of this statement with solvability; this is the open statement itself
  amenable-finite-cd-integral-group-rings-are-domains: that is the zero-divisor statement in all dimensions; in dimension 2 it is equivalent to this one; in higher dimensions coherence of Q[G] forces every finitely generated subgroup to be of type FP_2 over Q, which is not expected for all solvable groups of finite cd, so only the principal-ideal form of the criterion transfers there
  characteristic-zero-one-relator-group-algebras-are-coherent: that proves coherence from a one-relator presentation; here no presentation is given and amenability is the only structural input
---

**OPEN.** Let `G` be an amenable group with `cd_Z G = 2`. Then `Q[G]` is left coherent.

By `amenable-cd-two-solvable-iff-coherent-rational-group-algebra` this is equivalent to
Kropholler's question for groups of cohomological dimension at most 2, and to the zero-divisor
statement `amenable-finite-cd-integral-group-rings-are-domains` restricted to dimension 2.

**Weakest sufficient form.** It suffices that every principal left ideal `Q[G]a` is finitely
presented, i.e. that `ann_l(a)` is finitely generated for every `a ∈ Q[G]`. Indeed `pd Q[G]a <= 1`
because `cd_Q G <= 2`, so `ann_l(a)` is projective, and a finitely generated one has integral
`L²`-dimension, which forces it to vanish
(`amenable-principal-fp-group-algebras-are-domains-proof`, Step 2).

**Where it sits.** Jaikin-Zapirain and Linton prove coherence of `K[G]` for many two-dimensional
groups through vanishing `L²`-Betti numbers of subgroups, but their method presupposes a
Hughes-free division ring (strong Atiyah), i.e. the domain property this claim is meant to give.
Every subgroup of an amenable group has vanishing `L²`-Betti numbers, so the `L²` input is
available; what is missing is only the embedding into a division ring.

## Attempts

- **2026-09-17 (lane `sw-112`): Fox-rank attainment, dies at strong Atiyah.** By
  `amenable-fp-iff-affiliated-top-homology-vanishes` (item 4), for finitely generated `G` this
  claim is equivalent to `H_1(G; U(G)) = 0`, i.e. to some finite set of relators having a Fox
  Jacobian of von Neumann rank `d - 1`. Amenability gives `dim_U H_1(G; U(G)) = 0`, so the ranks of
  the truncated Jacobians increase to `d - 1`. The attack tried to force attainment from
  integrality of these ranks. It dies because integrality of von Neumann ranks of matrices over
  `Q[G]` is the strong Atiyah conjecture over `Q` for `G`, and for torsion-free amenable `G` that is
  equivalent to `Q[G]` being a domain, which is the claim itself. Dimension counting alone never
  makes the relation module finitely generated.
