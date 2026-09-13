---
rg: 2
id: every-type-fn-group-embeds-in-a-type-fn-plus-1-group
kind: claim
title: "Every group of type F_n (n >= 2) embeds in a group of type F_{n+1}"
artifacts:
  - research/artifacts/zp-z1-01-higher-rope-defects-2026-09-13.md
distinct_from:
  some-type-fn-group-embeds-in-no-type-fn-plus-1-group: that is the negation of this claim
---

For every `n >= 2` and every group `G` of type `F_n` there are a group `H` of
type `F_{n+1}` and an injective homomorphism `G -> H`. This is the affirmative
answer to the first part of Zaremsky Problem 1.1 (root
`zaremsky-1-01-type-fn-groups-embed-in-type-fn-plus-1`).

Equivalent forms (proofs in the root body): for every finite `m >= 3`, a
universal finitely presented group embeds in a group of type `F_m`;
equivalently, every finitely generated recursively presented group embeds in a
group of type `F_m`. The claim follows from
`every-finitely-presented-group-embeds-in-an-f-infinity-group` through the
route `type-fn-plus-1-hosts-from-f-infinity-hosts`.

## Attempts

- **Higman's rope trick: dead above `FP_2`.** Fournier-Facio--Zaremsky,
  arXiv:2607.21727v1, Theorem B (`higman-rope-trick-group-is-never-fp3`): for
  infinite `G = F/R` with `R != 1`, the rope-trick group `Hig_ι(G)` has
  infinite-dimensional `H_3(-; Q)`. Leary's `FP_2` embedding (arXiv:1610.05813)
  uses the same device: their Remark 2.2 describes Leary's container as the
  rope-trick HNN extension ([Lea18a, Lemma 2.2]).
- **Graph-of-groups hosts with the input in a vertex group, over edge groups
  of type `FP_{n+1}`: dead.** If a finite graph of groups with `FP_{n+1}` edge
  groups has fundamental group of type `FP_{n+1}`, then every vertex group is
  of type `FP_{n+1}`, and a retract of such a group is too. So the input cannot
  be a factor or retract of a vertex group. The rope trick escapes this only
  because its edge group, the double `F *_R F`, is not of type `FP_2`. A proof
  node lands next.
- **Twisted Brin--Thompson hosts `SV_G`: they transmit finiteness, they do not
  raise it.** The criteria recorded in the graph ask the acting group `G`
  itself to be of type `F_n` (type `[A_n]`, Fournier-Facio--Wu--Zaremsky
  arXiv:2603.24687v2, Definition 1.3; at `n = 2` the criterion is an
  equivalence, `twisted-brin-thompson-finite-presentation-criterion`).
- **Ascending-HNN lever (Fournier-Facio--Zaremsky Theorem A): live.** If the
  universal finitely presented group `U` embeds in a recursively presented
  group `H` of type `FP_m`, then `U -> H -> U` (Higman), and the ascending HNN
  extension of `U` along the composite is finitely presented and is also an
  ascending HNN extension of `H`. So it is of type `FP_m`, hence `F_m`. It
  therefore suffices to find recursively presented hosts of type `FP_m`, and
  homological finiteness allows infinitely presented hosts.
- **Size constraints on one universal host.** A group containing `U` contains
  Thompson's group `F` (infinite cohomological dimension) and every finite
  group. So a single universal host cannot have finite cohomological dimension,
  for instance cannot act freely on a finite-dimensional contractible complex.
- **Next target (open, unreviewed).** A higher rope: an HNN extension of
  `P x G` along an edge group `L'` whose homological defect, measured with
  coefficients in products of free modules, maps isomorphically onto that of
  `G` in every degree. A preliminary computation indicates that the direct
  variant (`L' -> G` with `FP_∞` kernel, `P` acyclic of type `FP_∞`) fails:
  on such coefficients the side `ι x 1` factors through `P` and contributes
  nothing. Work in progress in the lane artifact.
- **Level three, `n = 2` (lane z1-01-ffz-fp3).** The case `n = 2` is
  `every-finitely-presented-group-embeds-in-an-f3-group`. This claim implies
  it through `f3-hosts-for-fp-groups-from-type-fn-plus-1-hosts`. Two
  obstructions are established there:
  `fp2-vertex-graph-of-groups-infinite-h2-edge-kills-fp3` and
  `twisted-rope-trick-container-is-not-fp3-over-fp2-hosts`. The live explicit
  candidate is `acyclic-host-twisted-rope-container-is-of-type-fp3`. It
  differs from the product rope above: `α` lands in a group `P_0` that is only
  known to be finitely presented, and `ker π` is not of type `FP_∞`.
