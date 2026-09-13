---
rg: 2
id: residual-finiteness-of-finite-presentations-is-pi2-complete
kind: claim
title: Residual finiteness of finitely presented groups is Pi-zero-two complete
distinct_from:
  rf-fp-completeness-reduces-to-subgroup-separability-hardness: that reduces this cell to separability of finitely generated subgroups of F x F; this is the completeness statement itself, proved by a machine-built family that uses no separability input.
  residual-finiteness-of-enumerated-presentations-is-pi3-complete: that classifies recursive and enumerated presentations at level three and supplies the Pi-zero-two upper bound on finite presentations; this is the matching lower bound on finite presentations.
  kms-arbitrarily-hard-fp-rf-groups: that imports hard decidable word problems inside finitely presented residually finite groups; this is about recognizing residual finiteness among finite presentations.
artifacts:
  - research/artifacts/rf-fp-pumped-minsky-part1-2026-09-12.md
  - research/artifacts/rf-fp-pumped-minsky-part2-2026-09-12.md
  - research/artifacts/rf-fp-pumped-minsky-part3-2026-09-12.md
---

ESTABLISHED (proof written, unreviewed).  For the recursive coding of finite
group presentations,

```text
RF_fp     is Pi^0_2-complete,
NONRF_fp  is Sigma^0_2-complete.                                   (RFC1)
```

Moreover the hardness reduction lands in finitely presented groups of the
variety `A_p^2 A`, which are solvable of derived length at most three.  So
residual finiteness is already `Pi^0_2`-complete among finitely presented
**amenable** groups.  Those groups are all sofic, hyperlinear, weakly sofic
and MF, so the hardness of exact finite approximation is independent of every
metric approximation property.

This closes cell 3 of [[open-cells-arithmetical-complexity-of-group-properties]]
(the "residually finite Higman problem" cell of
[[arithmetical-complexity-table-of-group-properties]]), and with it the LEF
cell ([[lef-of-finite-presentations-is-pi2-complete]]).

**The reduction.**  `e |-> G(P(M_e))`, where:

- `M_e` is a clocked Minsky search machine that is universally halting iff
  `e in INF`;
- `P(M_e)` adds a pump and a drain;
- `G(-)` is the Kharlampovich--Myasnikov--Sapir group of a machine
  ([[kms-minsky-machine-groups-simulate-their-machines]]).

Universal halting gives residual finiteness through one periodic Rees quotient
of the machine semigroup.  A divergent configuration gives a nontrivial word
that every finite quotient identifies with the stop word: an idempotent power
of the pumping operator on the finite image of the abelian normal subgroup
lets the pumped input be drained.  See [[rf-fp-completeness-via-pumped-minsky-groups]].

**Structural reading.**  Deciding whether an infinite finitely presented
symmetry is residually finite requires exactly the `forall exists` quantifier
pattern, "every element eventually meets a finite witness".  No algorithm can
do better, even when all the groups involved are amenable.  The obstruction
lives in the dynamics of a machine, not in any Higman embedding.

**Also obtained** (part 3 of the artifact): residual finiteness of finitely
presented semigroups is `Pi^0_2`-complete; and the set of finite presentations
on which McKinsey's algorithm decides the word problem is `Pi^0_2`-complete.

## Attempts (history)

1. **Subgroup separability in `F x F`**
   ([[rf-fp-completeness-reduces-to-subgroup-separability-hardness]]).  This
   gives no new leverage: finitely generated subgroups of `F x F` are fibre
   products over finitely presented quotients.  Their separability is residual
   finiteness of the quotient (KMS arXiv:1204.6506v5, Lemma 5.2 and
   Remark 5.4).
2. **Higman compilers.**  These die structurally.  The positive branch must
   consist of finitely presented residually finite groups, hence groups with
   decidable word problems, and the existing rope is not LEF
   ([[mikhailova-positive-rope-is-not-lef]]).  Machine groups need no
   embedding at all.
