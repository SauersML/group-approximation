---
rg: 2
id: leavitt-units-have-laminar-finite-subgroup-defect
kind: claim
title: Some laminar combination of finite-subgroup idempotents has zero class in K_0 of the binary Leavitt unit group algebra
distinct_from:
  sofic-amalgam-finite-subgroup-idempotent-traces-are-strict: that is the established obstruction for configurations whose intersection amalgam is sofic; this asks for a defect from a configuration whose amalgam escapes it.
  leavitt-evaluation-kernel-unitization-not-directly-finite: that asks for any invisible one-sided pair; this restricts the defect to a literal laminar combination of finite-subgroup idempotents, whose K_0 class is an integer combination of finite-subgroup classes.
  mixed-finite-subgroup-defects-need-infinite-generation: that is the finite-join exclusion for two subgroups; this is the existence question for any number of finite subgroups.
artifacts:
  - research/artifacts/finite-subgroup-combination-defects-2026-09-12.md
---

**OPEN.** Let `R^x = L_(F_2)(1,2)^x` and `S = F_2[R^x]`. Exhibit:
- finite subgroups `H_0, ..., H_k <= R^x`;
- a laminar family of idempotents from them: distinct nonzero idempotents, each in some
  `M_n(F_2[H_s])`, any two nested or orthogonal (as in
  `sofic-amalgam-finite-subgroup-idempotent-traces-are-strict`);
- a nonzero idempotent `d` in the span of `1` and the members, with `[d S^n] = 0` in `K_0(S)`.

**What it gives.**
- `[d S^n] = 0` gives `d S^n (+) S^m ~= S^m` for some `m`.
- An isomorphism `phi : S^m -> d S^n (+) S^m`, composed with the inclusion and projection of the
  second summand, gives `c a = I_m != a c`.
- So `S` is not stably finite, and by `leavitt-stable-finiteness-equals-direct-finiteness` not
  directly finite. This is route `laminar-finite-subgroup-defect-gives-kaplansky-failure`.

## Attempts

- **Two finite subgroups.** Dead at every join. Nested differences have strict rational rank
  (`nested-two-finite-subgroup-idempotents-have-strict-rank`), and their lifted trace is
  `r(e) - r(f)` whatever the join.
- **Sofic realizations.** Dead (`sofic-amalgam-finite-subgroup-idempotent-traces-are-strict`).
  This covers every configuration that occurs in some sofic group:
  - forest configurations;
  - configurations with a sofic, amenable, LEF or finitely generated linear join;
  - configurations whose intersection amalgam is sofic, or has a finite quotient separating the
    union of the subgroups.
- **Constants at any prefix levels.** Dead. They form one locally finite group, so any finite
  family lies in one finite subgroup, where LFT1 applies.
- **The directive's candidates.** Dead.
  - Dyadic permutation subgroups at any levels are constants.
  - A configuration using only an order-two and an order-three subgroup generating `Z/2 * Z/3`
    inside `V` has two subgroups, so it is excluded at every join.
  - Members supported in a 2-group `P` are free projectives over the local ring `F_2[P]`, so they
    add only multiples of `[S]` to the class.
- **What survives.** Every item below is needed:
  - at least three non-constant finite subgroups, for example Thompson conjugates;
  - a cycle of nontrivial pairwise intersections;
  - a configuration that occurs in no sofic group, so the intersection amalgam and the join
    `<H_0, ..., H_k>` are both nonsofic;
  - trace balance `m n + sum m_i r(x_i) = 0` with `d != 0`.

  Even then, `[d S^n] = 0` asks for more than the trace. Nothing has been constructed. The
  existence of a zero-trace laminar combination is intrinsic to the amalgam; see Section 3 of the
  artifact.
- **Cost of a candidate.**
  - A trace-balanced laminar configuration is checkable on finite data: the rectangles
    `(H_i x H_j)/D_ij`, the union of the `H_i`, and a rational identity.
  - Any such configuration, in any group, certifies that no sofic group contains it (artifact
    Section 3.5).
  - So this route cannot give a cheap candidate. It needs a finite configuration of finite groups
    that occurs in no sofic group, with modular cancellation in its table.
