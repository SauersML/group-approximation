---
rg: 2
id: mf-nonhyperlinear-residual-with-amenable-quotient-is-critical
kind: claim
title: An MF counterexample whose residual has amenable quotient contains an MF counterexample with no hyperlinear quotient
distinct_from:
  mf-nonhyperlinear-collapse-structure: that shows the residual R of a counterexample is infinite, contains no finite normal subgroup and has hyperlinear quotient; this adds that when G/R is amenable, R itself has no nontrivial hyperlinear quotient, and that for a Kazhdan counterexample G/R is infinite and non-amenable.
  mf-kazhdan-groups-with-normal-subgroup-property-are-hyperlinear: that settles Kazhdan MF groups with the normal subgroup property by treating a finite-index residual; this treats every residual with amenable quotient, of any index, and Kazhdan counterexamples without the normal subgroup property.
  mf-implies-hyperlinear: that asks whether every MF group is hyperlinear; this only constrains a counterexample.
---

**Statement.** Let `G` be a countable group that is MF in the weak
norm-matrix-corona convention of `mf-implies-hyperlinear` and is not
hyperlinear, and let `R` be its hyperlinear residual.

1. **Amenable quotient.** If `G/R` is amenable (in particular if `R` has
   finite index), then `R` is an MF group that is not hyperlinear and whose
   hyperlinear residual is `R` itself. Equivalently, every homomorphism from
   `R` into a hyperlinear group is trivial. In particular `R`:
   - is infinite and perfect;
   - has no nontrivial finite or amenable quotient;
   - has no proper finite-index subgroup;
   - has no nontrivial finite normal subgroup;
   - does not have property (T);
   - for every injective homomorphism `u` from `R` into the unitary group of
     the norm matrix corona, the assignment `u(g) -> 1` extends to a
     character of `C*(u(R))`.
2. **Kazhdan counterexamples.** If `G` has property (T), then `G/R` is an
   infinite, non-amenable, hyperlinear group with property (T). In particular
   `R` has infinite index.
3. **Reduction of a case of the root.** Suppose every nontrivial MF group has
   a nontrivial hyperlinear quotient. Then every MF group whose hyperlinear
   residual has amenable quotient is hyperlinear.
4. **Other quotient classes.** The conclusion of part 1 holds whenever `G/R`
   lies in a class `C` of hyperlinear groups such that every extension of a
   hyperlinear group by a member of `C` is hyperlinear.

**Scope.** This is a structural fragment of `mf-implies-hyperlinear`. A
counterexample either has a residual with non-amenable quotient, or contains
an MF counterexample with no nontrivial hyperlinear quotient at all. Part 2
recovers clause 2 of
`mf-kazhdan-groups-with-normal-subgroup-property-are-hyperlinear`: with the
normal subgroup property, the infinite residual would have finite index.

**Residually finite quotients give no chain argument.** Every finite-index
subgroup `H` of `G` containing `R` has hyperlinear residual `R`, by
`hyperlinear-visibility-transfers-across-finite-index`. So a chain of
finite-index subgroups above `R` never separates an element of `R`. Residual
restriction along residually finite quotients for all countable groups is
equivalent to hyperlinear-by-residually-finite permanence, by clause 2 of
`hyperlinear-residual-restricts-along-amenable-quotients`. The sofic analogue
of that permanence fails (`sofic-semidirect-product-closure-fails`: an
amenable lamp group extended by a residually finite group, not sofic). So a
proof for residually finite `G/R` must use the MF hypothesis on `G`, not only
the quotient structure.

No novelty is claimed.
