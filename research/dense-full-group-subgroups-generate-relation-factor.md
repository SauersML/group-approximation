---
rg: 2
id: dense-full-group-subgroups-generate-relation-factor
kind: claim
title: The unitaries of a uniformly dense countable subgroup of an ergodic full group generate the whole relation factor, so its fixed-point character is extremal with GNS factor L(R)
distinct_from:
  full-group-subgroup-trace-generation-dichotomy: that shows an essentially free subgroup generates only a proper subalgebra with the regular trace; this shows a dense (hence far from free) subgroup generates all of L(R) with the fixed-point trace.
  separable-ii1-factors-have-weakly-dense-full-free-group-cstar: that produces some weakly dense free-group C*-algebra in any separable II_1 factor with no trace constraint; this identifies the generated algebra for the canonical full-group unitaries, whose trace is the fixed-point character.
  character-diracization-limit: that studies powers of a non-CE character; this only identifies the GNS algebra of the fixed-point character of a dense subgroup.
---

**ESTABLISHED** by `dense-full-group-subgroups-generate-relation-factor-proof`.

**Statement.** Let `R` be an ergodic probability-measure-preserving countable equivalence relation on a standard
nonatomic probability space `(X, mu)`. Let `Gamma <= [R]` be a countable subgroup that is dense for the uniform
metric `d_u(phi, psi) = mu({x : phi x != psi x})`. Then

```text
W*(u_g : g in Gamma) = L(R),
```

and the fixed-point character `chi_R(g) = mu(Fix g)` of `Gamma` is an extremal character whose tracial GNS von
Neumann algebra is `(L(R), tau_R)`. In particular `chi_R` is Connes-embeddable on `Gamma` iff `L(R)` is.

Countable dense subgroups exist because `([R], d_u)` is separable when `R` is countable.
