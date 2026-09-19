---
rg: 2
id: torsion-free-sofic-kazhdan-group-without-finite-quotients
kind: claim
title: Some nontrivial torsion-free sofic Kazhdan group has no nontrivial finite quotient
distinct_from:
  lef-kazhdan-group-without-finite-quotients-exists: that group is LEF, Kazhdan and quotientless but has torsion (Weyl elements of EL_3); this asks for a torsion-free one, with only soficity.
  torsion-free-lef-kazhdan-kernel-with-exact-mapping-torus-radical: its prerequisite (L1) asks for a LEF such group and then adds (L2) and (L3); this is the bare intrinsic gate, with soficity in place of LEF and no mapping torus.
  hyperbolic-rf-gives-torsion-free-lef-quotientless-kazhdan: that is a conditional supply of a LEF member from residually finite stages; this is the open existence statement itself, which every flagship witness needs.
  relation-cover-rational-lifting-over-quotientless-kazhdan: that asks for a specific cover with clauses (RLT) and an induced envelope, whose output would be a member of this gate; this asks only for a member, by any construction.
  automorphic-sofic-kazhdan-kernel-with-full-mf-radical: that asks for a full-MF-radical kernel with a finite automorphic presentation; this drops the radical and the presentation and keeps only the intrinsic clauses forced on every kernel.
  titz-witzel-kernel-sofic: that asks soficity of one specific simple lattice, which would be a member; this asks for any member.
artifacts:
  - research/mapping-torus-mf-radical-lies-in-finite-residual.md
  - research/sofic-stages-give-torsion-free-quotientless-sofic-kazhdan.md
  - research/hyperbolic-rf-gives-torsion-free-lef-quotientless-kazhdan.md
---

**OPEN.** There is a nontrivial group `K` that is torsion-free, sofic and Kazhdan, and has no
nontrivial finite quotient. Call this the gate (Q_tf^sof).

## Why it is a gate: every flagship witness passes through it

Let `G = K ⋊_φ Z` be a witness for `torsion-free-sofic-exact-mf-radical-over-z`, so that
`Rad_MF(G) = K × {0}` with `K ≠ 1` Kazhdan. Then:

1. `K` is finitely generated, since it is a countable Kazhdan group.
2. `K` is torsion-free and sofic, since it is a subgroup of the torsion-free sofic group `G`.
3. `K` has no nontrivial finite quotient, by (FRB2) of
   `mapping-torus-mf-radical-lies-in-finite-residual`.

So `K` lies in the gate. A refutation of the gate kills the following all at once:
- the flagship;
- (P1) of region (IO-int);
- (L1) of `torsion-free-lef-kazhdan-kernel-with-exact-mapping-torus-radical`;
- the output of `relation-cover-rational-lifting-over-quotientless-kazhdan`.

## Why it is hard to refute

By `sofic-stages-give-torsion-free-quotientless-sofic-kazhdan` (ESTABLISHED,
conditional):

```text
not (Q_tf^sof)  ==>  every torsion-free cocompact Sp(n,1) lattice has a
                     torsion-free hyperbolic quotient that is not sofic.
```

So any disproof of the flagship that uses only the intrinsic properties of the kernel (torsion-free,
sofic, Kazhdan, quotientless) would answer Gromov's soficity question for hyperbolic groups
(`nonsofic-hyperbolic-group`), and in torsion-free form. This strengthens the w13 calibration in
`exact-kazhdan-radical-kernel-cannot-be-lef`, which reached only a non-residually-finite hyperbolic
group, and only from the weaker statement (EKL2-tf).

## Candidates

| candidate | torsion-free | Kazhdan | quotientless | sofic |
|---|---|---|---|---|
| `EL_3(LC(X,F_q) ⋊ Z)`, `EL_3(LC(X,Z) ⋊ Z)` | no (`steinberg-images-die-in-torsion-free-groups`) | yes | yes | yes (LEF) |
| Titz Mite--Witzel lattices | yes | yes | yes (simple) | open (`titz-witzel-kernel-sofic`) |
| OOS torsion-free monster over an `Sp(n,1)` lattice | yes | yes | yes | yes under (S_Γ) |
| relation covers `D` | yes | yes | yes | only when `D = Q` (`relation-cover-sofic-envelope-forces-trivial-kernel`) |

Every nontrivial member is infinite and not residually finite. So no member is linear, and no member is
finitely presented and LEF.

## Attempts

**Attempt 1 (2026-09-19, swarm-0917 w14-titz-last1): the monster over sofic stages. Conditional
success; the claim stays OPEN.**
- `sofic-stages-give-torsion-free-quotientless-sofic-kazhdan` supplies a member from (S_Γ). The
  only step is the closedness of soficity in the space of marked groups.
- Operator MF is not known to be closed in that space, so the same argument does not decide
  `Rad_MF(Q)`.
- (S_Γ) is open. Every Kazhdan quotient of `Γ` fails the cubulation route to soficity, as recorded in
  the "checked against" section of `hyperbolic-rf-gives-torsion-free-lef-quotientless-kazhdan-proof`.
