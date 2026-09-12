---
rg: 2
id: fp-self-similar-groups-with-arbitrarily-hard-word-problem
kind: claim
title: For every recursive time bound some finitely presented self-similar group has a harder word problem
distinct_from:
  fp-simple-groups-with-arbitrarily-complex-word-problem: that is the root asking for finitely presented SIMPLE groups beyond every recursive bound; this asks the same for finitely presented self-similar groups, and it implies that root through Zaremsky's embedding.
  every-fp-rf-group-embeds-in-fp-self-similar-group: that asks for a self-similar overgroup of EVERY finitely presented residually finite group; this asks only for one hard self-similar group per recursive bound, a much weaker existence statement that the embedding claim implies.
  kms-arbitrarily-hard-fp-rf-groups: that realizes arbitrarily hard word problems by finitely presented residually finite solvable groups with no tree action required; this requires the hard group itself to be finitely presented and self-similar.
---

**OPEN.** For every recursive `T: N -> N` there are `d >= 2` and a finitely
presented self-similar group `G <= Aut(T_d)` whose word problem has no
algorithm running in time `C*T(C*l) + C*l + C` for any constant `C`.

**Why it matters.**
- By `arbitrarily-complex-fp-simple-via-hard-self-similar-groups` it implies
  `fp-simple-groups-with-arbitrarily-complex-word-problem`, unconditionally.
  That would remove the only complexity-based counterexample route to
  `boone-higman-conjecture`: a counterexample from word-problem complexity alone
  needs a recursive bound shared by all finitely presented simple groups.
- By `rover-nekrashevych-word-problem-reduces-to-self-similar-group` it is
  also *necessary* for the Rover--Nekrashevych branch of that root. That
  construction never makes a simple host harder than its self-similar input,
  beyond exponential rescaling.

## Necessary conditions

- **Infinitely many states.** Automaton groups and contracting self-similar
  groups consist of rational homeomorphisms. Their word problems share one
  exponential bound (`rational-homeomorphism-subgroups-have-exponential-wp`), so
  the wall `complexity-bounded-host-classes-are-not-universal` excludes them as
  a family. A hard example must have a generator with infinitely many distinct
  sections, as condition (N2) of `every-fp-rf-group-embeds-in-fp-self-similar-group`
  already says for the stronger claim.
- **Residual finiteness.** Every self-similar group is residually finite and
  residually `W_d` (condition (N1) of the same node). Hard finitely presented
  residually finite groups exist (`kms-arbitrarily-hard-fp-rf-groups`), so this
  is a screen on `d`, not an obstruction.

## Attempts

1. **Through the embedding claim.** The route
   `hard-self-similar-groups-from-fp-rf-embedding` derives this claim from
   `every-fp-rf-group-embeds-in-fp-self-similar-group`, applied to the
   Kharlampovich--Myasnikov--Sapir groups. It is open because that embedding
   claim is open, and it asks for far more than one hard example per bound.
2. **Self-similar affine groups over rings.** Zaremsky's Example 4.7 in
   arXiv:2405.09722 (imported through `fp-self-similar-groups-embed-in-fp-simple-groups`)
   covers `R^n x| GL_n(R)` over suitable rings. It lands inside linear groups
   over fields, whose word problems are classically low complexity
   (Lipton--Zalcstein for characteristic 0, Simon for positive characteristic;
   not imported here). So it cannot supply hard examples.
   *Dead as a source.*
3. **Direct virtual-endomorphism construction.** Not yet attempted. A group
   with a finite-index subgroup `H` and a homomorphism `phi: H -> G` of trivial
   core acts faithfully and self-similarly on the `[G:H]`-regular tree
   (Nekrashevych--Sidki). The task is a family of finitely presented groups
   with hard word problems carrying such `phi`, with `phi` non-contracting
   (by the first necessary condition). This session did not check the
   solvable KMS groups for virtual endomorphisms of trivial core.
