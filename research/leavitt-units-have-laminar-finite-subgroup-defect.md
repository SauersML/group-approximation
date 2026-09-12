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
- **Localization to one star** (lane `w5-laminar-cycle`, 2026-09-12;
  `research/artifacts/laminar-cycle-overfilled-stars-2026-09-12.md`).
  - `laminar-defects-localize-to-a-nonsofic-overfilled-star`: any nonzero laminar combination with
    `t_p <= 0` contains a nonzero atom whose star (one parent and its orthogonal children) is
    *overfilled*, meaning `sum r(children) >= r(parent)`. That star alone occurs in no sofic group.
  - So candidates are decided star by star. A star inside a common finite subgroup or any sofic
    subgroup is dead, and a star with all subgroups in Thompson's `V` would certify `V` nonsofic.
- **Fake cycles.** `intersection-edges-inside-a-third-subgroup-are-redundant`: an edge `D_ij <= H_l`
  does not change the amalgam. A three-subgroup star needs every pairwise intersection strictly larger
  than the triple intersection. Artifact Example 2.4 is a fake cycle in `V` (the constants `S_4` with
  the partition groups of `{[0],[10],[11]}` and `{[000],[001],[01],[10],[11]}`): all edges are
  nontrivial and the join is infinite, yet the amalgam is virtually free.
- **Thompson conjugates of constants.** The trace question sees only the abstract star: the groups,
  their intersections and the identifications (artifact Remark 2.5). A conjugation that keeps the
  abstract intersection data changes nothing. Only conjugates that produce an intersection pattern
  occurring in no finite (or sofic) group can help.
- **Search inside `V`.** `finite-subgroups-of-thompson-v-permute-a-canonical-partition`: every finite
  `H <= V` sits in `Sigma(P_H) ~= Sym(|P_H|)` for a canonical coarsest cylinder partition, and
  `H n K <= Sigma(P_H ^ P_K)`. So V-hosted stars can be enumerated from partitions and tested with the
  essential-graph criterion.
- **Label realization in `V`.** `v-hosted-stars-without-block-symmetries-occur-in-finite-groups`: if
  every intersection element fixes all non-common partition pieces, the configuration occurs in
  `Sym(union of the P_s)` with exact intersections, so it is dead. Artifact Example 4.2 is an essential
  triangle of `S_7`'s in `V` with `S_4` intersections and an infinite join; it lives in `Sym(12)`. A
  V-hosted survivor needs *block symmetries*: intersection elements exchanging non-common pieces with
  identical relative substructure.
- **Where it stops.** No overfilled star has been constructed, and there is no obstruction for
  essential cycles whose amalgam has no sofic quotient injective on the union of the vertex groups.
  Candidate amalgams are colimits of nonpositively curved triangles of finite groups, such as hyperbolic
  colimits and exotic `A_2~`-lattices, whose soficity is open (literature not re-read).
