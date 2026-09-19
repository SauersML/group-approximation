---
rg: 2
id: hyperbolic-rf-gives-torsion-free-lef-quotientless-kazhdan
kind: claim
title: If the torsion-free hyperbolic quotients of one Sp(n,1) lattice are residually finite, its torsion-free Tarski monster quotient is an LEF Kazhdan group without finite quotients
distinct_from:
  lef-kazhdan-group-without-finite-quotients-exists: that gives an unconditional LEF Kazhdan quotientless group, EL_3 of a crossed-product ring, which contains Weyl elements of finite order; this gives a torsion-free one, conditionally on residual finiteness of hyperbolic groups.
  torsion-free-lef-kazhdan-non-rf-seed: that seed is torsion-free, LEF and Kazhdan but central-by-residually-finite, so it has finite quotients; the group here has none.
  kazhdan-torsion-free-tarski-monster-satisfies-kk: that constructs the same monsters and proves only trivial projections; this adds the local embedding into finite groups, which needs residually finite stages.
  torsion-free-kazhdan-alternating-mother-limit-gate: that asks for a torsion-free simple limit of alternating quotients of a Kazhdan mother; this gets a torsion-free quotientless LEF Kazhdan group from hyperbolic stages instead, conditionally.
  exact-kazhdan-radical-kernel-cannot-be-lef: that is the mapping-torus statement EKL1; this shows only that the torsion-free repair of its refuted statement EKL2 cannot be proved without answering Gromov's residual finiteness question.
  torsion-free-non-residually-finite-hyperbolic-group: that is the open existence question; this is an implication towards it and settles nothing in either direction.
---

**ESTABLISHED** by `hyperbolic-rf-gives-torsion-free-lef-quotientless-kazhdan-proof`, which uses
only the Olshanskii--Osin--Sapir construction as imported verbatim in
`kazhdan-torsion-free-tarski-monster-satisfies-kk-proof`.

## Statement

Let `Γ` be a torsion-free cocompact lattice in `Sp(n,1)`, `n ≥ 2`. Assume

```text
(RF_Γ)  every torsion-free hyperbolic quotient of Γ is residually finite.
```

Then the torsion-free Tarski monster quotient `Q` of `Γ` has all of the following properties:

- infinite, finitely generated, non-abelian and torsion-free;
- Kazhdan;
- LEF, hence sofic and operator MF;
- without nontrivial finite quotients.

It is not finitely presented, since a finitely presented LEF group is residually finite.

**Contrapositive (the calibration).** Consider the torsion-free repair of the refuted statement
(EKL2) of `exact-kazhdan-radical-kernel-cannot-be-lef`:

```text
(EKL2-tf)  a torsion-free LEF Kazhdan group without nontrivial finite quotients is trivial.
```

If (EKL2-tf) holds, then for every such `Γ` some torsion-free hyperbolic quotient of `Γ` is not
residually finite. In particular `torsion-free-non-residually-finite-hyperbolic-group` holds.

## What this kills

Class of approaches: prove that the kernel `K` of the goal `torsion-free-sofic-exact-mf-radical-over-z`
is not LEF, or that (EKL1) holds, using only intrinsic properties of `K`: finitely generated,
torsion-free, Kazhdan, no nontrivial finite quotient, sofic. Such arguments include:
- torsion-freeness certificates on finite models;
- weak quasidiagonality repaired by torsion-freeness;
- trace or spectral gaps on exact local models.

Where each one dies: it would prove (EKL2-tf). Under `(RF_Γ)` the monster `Q` has every one of these
properties and is LEF, so the argument would produce a non-residually-finite torsion-free hyperbolic
quotient of every such `Γ`. That answers Gromov's question.

So any proof of (EKL1) that does not also settle Gromov's question must use the mapping torus:
- the automorphism `ψ`;
- finite presentation of `K ⋊_ψ Z`;
- the exact radical.

This is the refined form of the "What remains" line of `exact-kazhdan-radical-kernel-cannot-be-lef`.

## What this does not do

- It does not produce a witness for the goal. It is not known whether `Q` has an automorphism of
  infinite outer order, or a finitely presented mapping torus.
- Remark (proved in the route, section 4): for every automorphism `ψ`, `Q ⋊_ψ Z` contains no
  non-abelian free subgroup. So a finitely presented mapping torus of `Q` would fall under the
  Bieri--Strebel ascending-HNN constraints. Nothing further is claimed.
- It does not decide `(RF_Γ)`. Both `(RF_Γ)` and (EKL2-tf) remain open.
