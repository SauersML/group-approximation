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

ESTABLISHED.  Reviewed by `ex-verify-groups` (part 3 §3.2) and by
`ex-verify-logic-quantum` (part 1), and corrected after both reviews.  The
novelty pass by `ex-novelty` found no prior statement within its bound (see
Prior art below).  For the recursive coding of finite group presentations,

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
and the residual-finiteness entry of the finite-presentation column of
[[arithmetical-complexity-table-of-group-properties]], and with it the LEF
cell ([[lef-of-finite-presentations-is-pi2-complete]]).

**Framing.**  The completeness question is a cell framed by this repository;
no source found by the novelty pass prints it.  It must not be called "the
residually finite Higman problem".  The question KMS actually print in
arXiv:1204.6506v5 §1.1.7 is different: does every finitely generated
residually finite group with solvable word problem embed in a finitely
presented residually finite group?  Rauzy answered that negatively in
arXiv:2002.02540 (J. Group Theory): "There exists a finitely generated
residually finite group with solvable word problem, that does not embed in any
finitely presented residually finite group."

**Prior art and credit** (per the `ex-novelty` pass,
`research/artifacts/ex-novelty-rf-fp-pi02-pass-2026-09-13.md`, sources read
there).  No earlier statement of `Pi^0_2`-hardness or completeness of `RF_fp`
or `LEF_fp` was found within that bound.

- **Rauzy, arXiv:2111.01190v2** (IJAC 2025), Proposition "RF not CE": "The set
  of finitely presented residually finite groups is not computably enumerable
  (for ν_FP), and furthermore it cannot be contained in a ν_FP-c.e. set of
  finitely presented groups with uniformly solvable word problem."  It is
  proved from McKinsey and KMS.  This is the nearest printed lower bound, the
  `Sigma^0_1`-exclusion half of the placement.
- **Bridson--Wilton, arXiv:1401.2273** (Invent. Math. 2015): no algorithm
  decides whether a finitely presented group has a proper finite-index
  subgroup.
- **Rauzy, arXiv:2605.30138** (May 2026), appendix: residual finiteness is
  boldface `Pi^0_3`-complete in the space of marked groups.  The paper's
  introduction prints "Sigma^0_3-complete" for the same set.  This is
  topological, not the lightface index set, but it is the nearest prior art for
  [[residual-finiteness-of-enumerated-presentations-is-pi3-complete]].
- **KMS** supply the machine groups and the sufficiency theorem
  (sym-universal halting implies residually finite).  The converse used here,
  that a divergent pumped configuration kills residual finiteness, is not
  in KMS.

**The reduction.**  `e |-> G_0(P(M_e))`, where:

- `M_e` is a clocked Minsky search machine that is universally halting iff
  `e in INF`;
- `P(M_e)` adds a pump and a drain;
- `G_0(-)` is the Kharlampovich--Myasnikov--Sapir group of a machine
  ([[kms-minsky-machine-groups-simulate-their-machines]]) with the stop
  relations `x_(q_0 w) = 1` added
  ([[kms-group-with-stop-relations-simulates-all-words]]).

Universal halting gives residual finiteness through one periodic Rees quotient
of the machine semigroup.  A divergent configuration gives a nontrivial word
that every finite quotient kills: an idempotent power of the pumping operator
on the finite image of the abelian normal subgroup lets the pumped input be
drained to the stop word, which is `1`.  See
[[rf-fp-completeness-via-pumped-minsky-groups]].

**Structural reading.**  Deciding whether an infinite finitely presented
symmetry is residually finite requires exactly the `forall exists` quantifier
pattern, "every element eventually meets a finite witness".  No algorithm can
do better, even when all the groups involved are amenable.  The obstruction
lives in the dynamics of a machine, not in any Higman embedding.

**Also obtained** (part 3 of the artifact): residual finiteness of finitely
presented semigroups is `Pi^0_2`-complete; and the set of finite presentations
on which McKinsey's algorithm decides the word problem is `Pi^0_2`-complete.

**Review corrections.**
- The divergent input must carry `pi = 1 + e_tau(c)`.  This was found by `ex-verify-groups`.
- The group must carry the stop relations.  This was found by `ex-verify-logic-quantum`.
  Under KMS's displayed relations G1--G8, the words of distinct stop configurations are
  distinct, and the basis map `T -> T_1` is not injective.
- In the artifact parts, read `G_0` for `G`.
- Details: `research/artifacts/ex-review-logic-quantum-2026-09-12-part1.md`.

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
