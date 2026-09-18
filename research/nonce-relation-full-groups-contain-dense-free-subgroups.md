---
rg: 2
id: nonce-relation-full-groups-contain-dense-free-subgroups
kind: claim
title: The full group of a non-CE ergodic relation of cost below m contains a dense free group F_m whose fixed-point character generates the non-CE factor, so density and fixed-point data never certify non-hyperlinearity
distinct_from:
  diracization-gap-equals-nonhyperlinear-group: that records the free-group degeneracy of normal-Dirac promotion of an IRS character on F_2; this shows the degeneracy survives passage to the full group of the relation, where the subgroup is dense and its fixed-point character generates the entire non-CE factor.
  non-cohyperlinear-irs-exists: that gives a non-CE IRS character on F_2 whose GNS algebra is a proper subalgebra of the relation factor; this gives a free group whose fixed-point character has GNS algebra equal to the full non-CE relation factor and whose closure is the whole full group.
  full-group-subgroup-trace-generation-dichotomy: that separates trace from generation for one subgroup; this kills the class of promotion arguments that use only the uniform closure and the fixed-point GNS algebra.
  minimal-free-cantor-action-with-nonhyperlinear-full-group: that asks for a non-hyperlinear subgroup of a topological full group; this is an obstruction for measure full groups that does not decide that claim.
---

**ESTABLISHED** by `nonce-relation-full-groups-contain-dense-free-subgroups-proof`.

**Statement.**
1. There is an ergodic pmp countable equivalence relation `R_H` on a standard nonatomic probability space, generated
   by two automorphisms (so of cost at most 2), with `L(R_H)` not Connes-embeddable.
2. For every ergodic pmp relation `R` of cost `< m` with `L(R)` not CE, `[R]` contains a subgroup `Gamma ≅ F_m` that
   is dense for the uniform metric. For `R = R_H` one may take `m = 3`.
3. `Gamma` is hyperlinear, while its fixed-point character `chi_R(g) = mu(Fix g)` is extremal with tracial GNS
   algebra `(L(R), tau_R)`, which is not CE.

**Class killed.** Let `K` be the class of arguments that conclude "`Lambda` is non-hyperlinear" for a countable
`Lambda <= [R]` from hypotheses on the pair (uniform closure of `Lambda` in `[R]`, GNS algebra of `chi_R|Lambda`),
together with any property of `R` (ergodicity, finite cost, non-CE factor). The **invariant** is that pair. The pair
of a dense `F_3` in `[R_H]` is `([R_H], L(R_H))`, which is the largest possible value: the same as for `[R_H]`
itself, or for any dense subgroup. Every member of `K` dies at the **step** "the fixed-point character of a dense
subgroup is non-CE, hence the subgroup is non-hyperlinear", because `F_3` is hyperlinear.

Members of `K` include:
- "a dense subgroup of the full group of a non-CE relation is non-hyperlinear";
- "a finitely generated topological generator of `[R]` is non-hyperlinear";
- "a subgroup whose fixed-point unitaries generate a non-CE II_1 factor is non-hyperlinear".

With the tensor-power computation `chi_R^k <-> W*(u_g^(⊗k))`, the same witness also realizes the Diracization
free-group degeneracy of `diracization-gap-equals-nonhyperlinear-group`: `chi_R^k -> delta_e` pointwise, and the
limit is CE. That computation is not needed here and is not claimed.

**What survives.** A proof of non-hyperlinearity for a subgroup of `[R]` must use algebraic structure of the subgroup
that free groups lack, such as closure under cut and paste along a Boolean algebra. That is the input of
`dense-full-subgroup-without-ce-covariant-model`.
