---
rg: 2
id: every-countable-group-is-left-right-sofic
kind: claim
title: Every countable group is left-right sofic, i.e. every Mikhailova left-right action over a free cover is sofic
distinct_from:
  product-of-free-groups-set-actions-are-sofic: that asks it for every set action of every product of two free groups; this asks it only for the left-right actions of groups, and the two are equivalent by the Goursat reduction.
  mikhailova-left-right-action-current-frontier: that concerns the left-right action of one fixed quotient, the nonsofic property-(T) host; this asks it for all groups at once, and contains that case.
  f2xf2-admits-nonsofic-action: that asks about p.m.p. actions of F2 x F2 in Paunescu's sense; this is about actions on countable sets in the GKP sense.
---

OPEN. For every countable group `Q` and all epimorphisms `q_1 : F ↠ Q`,
`q_2 : F' ↠ Q` from countable free groups, the action
`F x F' ↷ Q`, `(u,v).h = q_1(u) h q_2(v)^-1`, is sofic (GKP Definition
2.1(5)). Equivalently, (MLF1) of
[[mikhailova-left-right-action-current-frontier]] is sofic for every finitely
presented group.

By [[product-free-set-actions-reduce-to-left-right-actions]] this is
equivalent to [[product-of-free-groups-set-actions-are-sofic]].

## Attempts

- **Soft closure (dies as a proof; lane ex3-pfg-positive).** The class of
  left-right sofic groups contains the amenable groups. It is closed under
  subgroups, finite products, marked-group limits and co-amenable overgroups
  ([[product-free-set-actions-reduce-to-left-right-actions]],
  [[left-right-sofic-closed-under-co-amenable-overgroups]]). So it
  contains LEA groups and their amenable extensions. But everything built this
  way is sofic. For Kazhdan groups, co-amenable overgroups add nothing beyond
  finite index. So soft closure never reaches a nonsofic or finitely presented
  non-residually-amenable Kazhdan quotient. Any proof must produce models in
  which kernel words act nontrivially while fixing the color point, per (MCC4)
  of [[mikhailova-left-right-soficity-is-one-color-code]].
- **Levelwise exactification and amplification (dies; frontier node items
  6--8).** Ioana's failure of very flexible permutation stability for
  `F_m x F_m` blocks exact commuting models. Standard amplification does not
  shrink commutator defect. The external color must be diffuse.
- **Where a counterexample must live (fence).** It suffices to find one
  finitely presented `H` with nonsofic (MLF1). Such an `H` is not LEA, has no
  co-amenable left-right sofic subgroup, and both Mikhailova kernels fail
  amenable separability
  ([[g-x-free-set-actions-sofic-when-kernel-amenably-separable]]). The
  repository's fixed nonsofic property-(T) host satisfies all of these, so it
  is the natural test case. For it, the (MCC2) witness is open.
- **Compiler (open, not attempted here).** The first rope needs only the
  instance `H = H_e`, the Higman host, on `INF`
  ([[compiler-rope-edge-is-not-co-amenable]], (R3)). By the co-amenable
  overgroup theorem it would suffice that some co-amenable subgroup of `H_e` on
  `INF` is left-right sofic, e.g. the kernel of a homomorphism onto an amenable
  group, if it is LEA. The Higman construction has not been analyzed for such
  a subgroup.
