---
rg: 2
id: every-fp-rf-group-acts-on-a-regular-rooted-tree
kind: claim
title: Every finitely presented residually finite group acts faithfully on some regular rooted tree
refuted_by:
  - some-fp-rf-group-acts-on-no-regular-rooted-tree
distinct_from:
  some-fp-rf-group-acts-on-no-regular-rooted-tree: that is the negation, a single finitely presented residually finite group with no faithful regular-tree action; this is the universal positive statement, which is the first prerequisite of the split of every-fp-rf-group-embeds-in-fp-self-similar-group.
  every-fp-rf-group-embeds-in-fp-self-similar-group: that asks for a finitely presented self-similar overgroup; this asks only for a faithful action on T_d, which the overgroup would give and which is strictly weaker a priori.
---

**OPEN.** For every finitely presented residually finite group `G` there is
`d >= 2` such that `G` embeds in `Aut(T_d)`.

**Equivalent form.** Fix a finite presentation of `G`. Then `G` embeds in
`Aut(T_d)` iff for every `g != 1` there are `n` and a homomorphism
`G -> Aut(X^{<=n})` under which `g` survives. By
[[fp-tree-groups-have-computable-faithful-tree-actions]], the action can then
be chosen computable, uniformly in `(G, d)`.

**Necessary condition, and known cases.** (N1) must hold: `G` is residually
`W_d` for some `d`, so its torsion has boundedly many primes. The statement
holds for:
- virtually residually-`p` groups;
- finitely generated linear groups;
- the finite-class KMS groups, by
  [[finite-class-kms-groups-act-on-regular-rooted-trees]].

Candidate counterexamples are tracked under
[[some-fp-rf-group-acts-on-no-regular-rooted-tree]] and
[[fp-rf-group-with-unbounded-prime-torsion]].

## Attempts

1. **Enumerate truncated-tree quotients (2026-09-17).** For a finitely
   presented `G` the homomorphisms `G -> Aut(X^{<=n})` can be enumerated, and
   hanging them below the ray `1^infinity` gives a tree action. That action is
   faithful exactly when these quotients separate points. See
   [[fp-tree-groups-have-computable-faithful-tree-actions]].
   - *What it settles.* Computability.
   - *Where it dies.* It does not help with existence. Residual finiteness gives
     finite quotients, but no bound on their composition factors. So the attack
     dies at showing that a single `d` works, i.e. at (N1) for arbitrary
     finitely presented residually finite groups.
