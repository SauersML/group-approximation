---
rg: 2
id: ce-relation-full-group-subgroups-are-hyperlinear
kind: claim
title: If a pmp equivalence relation has a Connes-embeddable von Neumann algebra, every countable subgroup of its measure full group is hyperlinear
distinct_from:
  measure-full-group-subgroups-hyperlinear-if-crossed-product-ce: that treats topological full groups of an essentially free Cantor action through the crossed product; this treats the measure full group of an arbitrary countable pmp relation, including non-free actions, through the relation factor.
  full-group-subgroup-trace-generation-dichotomy: that shows a full-group subgroup cannot regenerate the relation factor as a group factor; this is the positive transfer from a CE relation factor to hyperlinearity of every countable subgroup.
  tree-lattices-hyperlinear-if-f2xf2-crossed-products-ce: that transfers CE of crossed products of one acting group to lattices; this needs no acting group and no freeness.
---

**ESTABLISHED** by `ce-relation-full-group-subgroups-hyperlinear-proof`. No novelty is claimed for the
argument; it is recorded as the base entry of the measure-full-group dictionary used by
`nonhyperlinear-via-full-subgroup-covariant-models`.

**Statement.** Let `R` be a countable probability-measure-preserving equivalence relation on a standard
probability space `(X, mu)`, `[R]` its measure full group (measure-preserving automorphisms whose graph lies in
`R`, modulo null sets) and `L(R)` its von Neumann algebra with trace `tau_R`. If `L(R)` is Connes-embeddable,
then every countable subgroup of `[R]` is hyperlinear.

**Contrapositive fence.** A non-hyperlinear subgroup of a measure full group can only live in `[R]` for a relation
with non-CE factor, and then its own orbit subrelation must already be non-CE. A search for a witness inside
measure full groups must start from a non-CE relation such as the one of
`non-ce-property-t-equivalence-relation-exists`.

**Dictionary (entropy-measure family, measure full group).**

| relation side | group/character side |
|---|---|
| `phi in [R]` | unitary `u_phi in L(R)` |
| `mu(Fix phi)` | `tau_R(u_phi)`, the fixed-point character |
| uniform metric `mu(phi != psi)` | `||u_phi - u_psi||_2^2 / 2` |
| `L(R)` CE | fixed-point character CE on every subgroup; every countable subgroup hyperlinear (this claim) |
| dense subgroup of `[R]` | its unitaries generate `L(R)` (`dense-full-group-subgroups-generate-relation-factor`) |
| support axiom `pi(g) e(1_Fix g) = e(1_Fix g)` | trace of the model is the fixed-point character (`support-covariant-models-carry-fixed-point-trace`) |
