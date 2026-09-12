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
- a laminar family `x_i in M_n(F_2[H_i])`, meaning any two members are nested or orthogonal (as
  in `sofic-amalgam-finite-subgroup-idempotent-traces-are-strict`);
- a nonzero idempotent `d` in the span of `1` and the `x_i`, with `[d S^n] = 0` in `K_0(S)`.

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
- **Sofic amalgams.** Dead (`sofic-amalgam-finite-subgroup-idempotent-traces-are-strict`). This
  covers forest configurations, and configurations with a sofic, amenable, LEF or finitely
  generated linear join.
- **Constants at any prefix levels.** Dead. They form one locally finite group, so any finite
  family lies in one finite subgroup, where LFT1 applies.
- **2-groups.** They contribute nothing: `F_2[P]` is local for a 2-group `P`. So dyadic involution
  subgroups, and `Z/2 * Z/3` inside `V`, reduce to the odd-order parts, which are excluded above.
- **What survives.** Every item below is needed:
  - at least three non-constant finite subgroups, for example Thompson conjugates;
  - a cycle of nontrivial pairwise intersections;
  - a nonsofic intersection amalgam;
  - trace balance `m n + sum m_i r(x_i) = 0` with `d != 0`.

  Even then, `[d S^n] = 0` asks for more than the trace. Nothing has been constructed. The
  existence of a zero-trace laminar combination is intrinsic to the amalgam; see Section 3 of the
  artifact.
