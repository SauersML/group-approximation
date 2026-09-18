---
rg: 2
id: q34-from-bffhz-q32-for-fp-simple-groups
kind: route
title: A finitely presented image of the relative automorphism action is a type (A) actor containing S, so Theorem C gives a finitely presented simple MIF overgroup
target: fp-simple-groups-embed-in-fp-simple-mif-groups
requires:
  - bffhz-q32-for-fp-simple-groups
  - relative-automorphism-action-is-highly-transitive
  - fp-simple-highly-transitive-groups-satisfy-pbh
  - simple-envelope-forces-solvable-word-problem
---

Let `S` be a finitely presented simple group.

**Finite `S`.** It embeds in Thompson's `V`, which is finitely presented, simple
and MIF. (`V` is highly transitive, hence MIF, by BFFHZ as recorded in
`fp-simple-group-with-nonrecursive-mixed-identities` Attempt 1.) From here on `S`
is infinite.

**Step 1 (the actor).** Put `A = Aut_S(S * F_2)`, `X = Hom_S(S * F_2, S) ≅ S^2`,
`K = ker(A ↷ X)` and `Q = A/K`.
- By `bffhz-q32-for-fp-simple-groups`, `Q` is finitely presented.
- `Q` acts faithfully on `X` by construction.
- By `relative-automorphism-action-is-highly-transitive` (BFFHZ Propositions 2.3
  and 2.6), the action of `A` is highly transitive and its point stabilizers are
  finitely generated. The stabilizers in `Q` are their images, so they are
  finitely generated.
- High transitivity leaves exactly two orbits on `X × X`: the diagonal and its
  complement.

So `Q ↷ X` is an action of type (A) (faithful, finitely presented actor,
finitely generated stabilizers, finitely many orbits of pairs).

**Step 2 (S sits in Q).** For `s in S`, let `t_s in A` fix `S` and `x_2` and
send `x_1` to `x_1 s`. Then `t_s t_(s')(x_1) = x_1 s s'`, so `s -> t_s` is a
homomorphism. For `φ in X`, `(φ ∘ t_s)(x_1) = φ(x_1) s`, which differs from
`φ(x_1)` when `s != 1`. So `t_s` moves every point, `t_s` is not in `K`, and
`S` embeds in `Q`. The same observation is recorded in
`relative-automorphism-action-is-highly-transitive` ("Why this graph carries it").

**Step 3 (Theorem C).** `S` is finitely generated with solvable word problem
(`simple-envelope-forces-solvable-word-problem`). It embeds in `Q`, which has an
action of type (A), so `S` satisfies (i) of BFFHZ Theorem C
(`fp-simple-highly-transitive-groups-satisfy-pbh`). By (i) ⟹ (iv), `S` embeds in
a finitely presented simple MIF group. `∎`

**Scope.** For each `S` the route uses Question 3.2 only at `n = 2`. Every
known obstruction to that instance is a condition on `J_1(S)`:
- recursiveness (`a2-kernel-removal-forces-recursive-kernel` (c));
- a finite basis over overgroups
  (`bffhz-q32-forces-finitely-based-mixed-identities`).

A group with `J_1(S)` not finitely based would make this route fail for `S` at
every `n`.
