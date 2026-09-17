---
rg: 2
id: amenable-cd-two-solvable-iff-coherent-group-algebra-proof
kind: route
title: Coherence gives domains by integral traces, domains give solvability by Degrijse, solvable cd-2 groups have coherent algebras
target: amenable-cd-two-solvable-iff-coherent-rational-group-algebra
requires:
  - amenable-principal-fp-group-algebras-are-domains
  - characteristic-zero-one-relator-group-algebras-are-coherent
artifacts:
  - research/artifacts/kropholler-question-zero-divisor-split-2026-09-16.md
---

Let `G` be amenable with `cd_Z G <= 2`. Then `G` is torsion-free (a finite cyclic subgroup has
infinite cd) and `cd_Q G <= cd_Z G <= 2`.

**(2) ⇒ (3).** By `amenable-principal-fp-group-algebras-are-domains`, item 3, `Q[G]` is a domain,
and `Z[G] ⊆ Q[G]` is a nonzero unital subring, hence a domain.

**(3) ⇒ (1).** If `cd G = 0`, `G = 1`. If `cd G = 1`, `G` is free (Stallings--Swan) and amenable,
so `G ≅ Z`. If `cd G = 2`, D. Degrijse, "Amenable groups of finite cohomological dimension and the
zero divisor conjecture", arXiv:1609.07635 (Math. Ann. 386 (2023)), Theorem B: an amenable group
of cohomological dimension 2 whose integral group ring is a domain is solvable. (Recorded with
quotes in the artifact, Proposition 3.1.)

**(1) ⇒ (2).** By Gildenhuys' classification (D. Gildenhuys, "Classification of soluble groups of
cohomological dimension two", Math. Z. 166 (1979)), together with the cases `cd <= 1` above, a
solvable group of cd at most 2 is `1`, `Z`, a noncyclic subgroup `A <= Q`, or
`BS(1,m) = <a, t | t a t^-1 = a^m>` with `m != 0`. Degrijse quotes the same list in Theorem B.

- `Q[1] = Q` is a field.
- `BS(1,m)` (which includes `Z^2 = BS(1,1)` and the Klein bottle group `BS(1,-1)`) is a one-relator
  group, and `Z = <a, t | t>` is one too, so `Q[G]` is coherent by
  `characteristic-zero-one-relator-group-algebras-are-coherent` (Jaikin-Zapirain--Linton,
  Theorem 1.1(2)).
- `A <= Q` is a directed union of infinite cyclic subgroups `C_i`, with `Q[C_i] ≅ Q[t^{±1}]` a
  principal ideal domain. A finitely generated left ideal `I` of the commutative domain `Q[A]` has
  its generators in some `Q[C_i]`, where they generate a principal ideal `(f)`, so `I = Q[A] f`.
  Since `Q[A]` is a domain, `I ≅ Q[A]` is free, hence finitely presented. So `Q[A]` is coherent.

This proves the equivalence. ∎

**Consequence for the root.** A counterexample to Kropholler's question of dimension at most 2 is
exactly an amenable group `G` with `cd G = 2` and `Q[G]` not left coherent. By
`amenable-principal-fp-group-algebras-are-domains` it even has an element `a` with `Q[G]a` not
finitely presented (a principal-ideal failure of coherence): otherwise every `Q[G]a` would be
finitely presented with projective annihilator (`pd <= 1`), hence of type `FP`, and `Q[G]` would
be a domain.
