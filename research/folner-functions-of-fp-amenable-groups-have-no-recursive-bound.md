---
rg: 2
id: folner-functions-of-fp-amenable-groups-have-no-recursive-bound
kind: claim
title: No recursive function eventually bounds the Følner functions of all finitely presented amenable groups
distinct_from:
  recursive-amenable-classes-have-uniform-folner-bounds: that is Cavaleri's theorem giving a recursive bound for each c.e. class of amenable presentations; this asserts that the class of all finite presentations of amenable groups has no such bound, the negative answer to Gromov's universal question.
  thompson-f-folner-function-exceeds-every-tower: that is a tower lower bound for the one group F, conditional on its amenability; this asks for lower bounds beyond every recursive function, necessarily through infinitely many groups.
---

**OPEN.** For every recursive `U: N -> N` there is a finite presentation
`<X | R>` of an amenable group whose Følner function `F_(Γ,X)` is not eventually
`<= U`.

This is the negative answer to Gromov's question (d), quoted in
`recursive-amenable-classes-have-uniform-folner-bounds`. Each single group has a
recursive bound, by Cavaleri's Theorem 3.1, so the claim is about infinitely
many groups. Through Corollary 3.6 it implies
`amenable-finite-presentations-are-not-recursively-enumerable`.

**Subgroups pass hardness upward** (proved here). Let `H = <Y> <= G = <X>` with
`Y ⊆ X`, and let `Ω` be an `n`-Følner set of `G`. Split `Ω` along right cosets,
`Ω_c = Ω ∩ Hc`. For `y in Y` we have `yΩ ∩ Hc = yΩ_c`, so

```text
sum_c sum_(y in Y) |Ω_c \ yΩ_c|  <=  |Y| |Ω| / n  =  sum_c |Y| |Ω_c| / n.   (FNB1)
```

Some `c` satisfies the inequality termwise. Then `Ω_c c^-1` is an
`(n/|Y|)`-Følner set of `H` of size at most `|Ω|`, so `F_(H,Y)(n) <= F_(G,X)(|Y| n)`.
It therefore suffices, for each recursive `U`, to put one finitely generated
amenable group with Følner function beyond `U` inside a finitely presented
amenable group.

## Attempts

1. **Fast Følner functions plus an amenable envelope.**
   - *Inputs exist.* Cavaleri's introduction reports Erschler's groups with
     arbitrarily fast Følner functions, and Brieussel--Zheng realizing every
     non-decreasing function up to equivalence. Neither primary source was read
     here.
   - *The missing step.* For recursive `U` one would need such groups to be
     recursively presented (unchecked) and to embed in finitely presented
     *amenable* groups. The second is an amenability-preserving Higman embedding,
     which the root records as unknown in general.
2. **Iterated wreath products.** Per Cavaleri's introduction, Erschler shows the
   `k`-fold iterated wreath product of `Z` has Følner function the `k`-th
   tetration.
   - *The envelope case.* For `k = 2` the Baumslag--Remeslennikov group is a
     finitely presented metabelian envelope.
   - *Where it dies as a method.* Any family with bounded nesting stays below a
     fixed tower, and towers are primitive recursive. Beating every recursive `U`
     needs non-primitive-recursive growth, one group per bound.
3. **Kharlampovich--Myasnikov--Sapir groups.** These have arbitrarily large Dehn
   and depth functions, but those are not Følner lower bounds.
   - *Structure.* Each group is an elementary abelian `p`-group spanned by
     configuration elements, extended by a fixed lamplighter-type metabelian
     group (arXiv:1204.6506v5, Lemmas 4.4--4.14).
   - *Expected bound.* Følner sets supported on bounded windows over Følner sets
     of the metabelian quotient are expected to give a bound independent of the
     machine. This is not proved, and it is recorded as a warning, not as a
     theorem.
4. **Thompson's group F.** Moore's tower bound
   (`thompson-f-folner-function-exceeds-every-tower`) forces growth beyond every
   fixed tower *if* `F` is amenable. Even then `F` is a single group, with a
   recursive bound by Cavaleri, so it cannot settle this claim.
