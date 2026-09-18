---
rg: 2
id: aperiodic-point-stabilizers-in-germ-extensions-of-v-are-not-fg
kind: claim
title: In a group of Cantor homeomorphisms containing V, the stabilizer of a non-eventually-periodic point where every element is locally a prefix replacement is not finitely generated
distinct_from:
  v-point-stabilizers-are-ascending-hnn-extensions-of-v: that shows the stabilizer of the eventually periodic point 0^∞ in V is an ascending HNN extension of V, hence F_∞; this shows that at non-eventually-periodic points the stabilizer is an ascending union of proper subgroups, hence not finitely generated.
  finitely-singular-tree-hosts-have-no-fg-stabilizers: that kills finitely generated stabilizers for finitary local-rule actions on trees by a singular-depth filtration; this is the Cantor-set statement for prefix-replacement hosts at aperiodic points, by a germ argument.
  twisted-brin-thompson-wp-equals-actor-orbit-problem: that shows point-stabilizer membership of a type (A) actor enters the word problem of SV_G; this shows such stabilizers cannot come from aperiodic points of V-like hosts, where membership would be as hard as computing the point.
---

**ESTABLISHED** (lane proof, elementary, not independently reviewed; no priority claimed).

## Statement

Let `C = {0,1}^N` and let `Γ ≤ Homeo(C)` contain Thompson's group `V`. Let `x ∈ C` be a point that is
**not eventually periodic**, and suppose every `g ∈ Γ` with `g(x) = x` agrees near `x` with a prefix
replacement `pw ↦ qw`. That holds when `x` is not a singular point of any element: every element of `V`,
and every element of a finite germ extension of `V` away from its singular set, is locally such a
replacement. Put `C_n = C_{x_0 ... x_{n-1}}`.

1. **Germ triviality.** Every `g ∈ Stab_Γ(x)` is the identity on some `C_n`.
2. **Ascending union.** `Stab_Γ(x) = ∪_n K_n`, with `K_n = {g ∈ Γ : g|_{C_n} = id}` and `K_n ⊊ K_{n+1}`.
3. **No finite generation.** `Stab_Γ(x)` is not finitely generated.
4. **No type (A) from aperiodic points.** Let `x` be as above and suppose the hypothesis holds at every point of
   the orbit `Γ·x`, for instance when `x` is not in the `Γ`-orbit of a singular point. Then the action of `Γ`
   on `Γ·x` is never of type (A) (`type-a-action-gives-boone-higman-for-subgroups`, condition 3), even though
   for `Γ = V` it is highly transitive.
5. **The same in `nV`.** Take `Γ ≤ Homeo(C^n)` containing `nV`, and a point `x` all of whose `n` coordinates
   are not eventually periodic, with the same local hypothesis. Items 1–3 hold with cones replaced by
   bricks.

## Proof

1. Near `x`, `g` maps `C_p ∋ x` by `pw ↦ qw`. Then `x = p·σ^{|p|}(x)` and `g(x) = q·σ^{|p|}(x) = x`. So `q`
   is a prefix of `x` and `σ^{|q|}(x) = σ^{|p|}(x)`. If `|p| ≠ |q|`, this equality makes `x` eventually
   periodic, which it is not. So `|p| = |q|`, then `q = x_{<|q|} = p`, and `g` is the identity on `C_p`.
   Take `n = |p|`.
2. Each `K_n` is a subgroup contained in `Stab_Γ(x)`, the `K_n` increase, and by item 1 their union is the
   stabilizer. For strictness, let `c` be the cone sibling to `C_{n+1}` inside `C_n`. `V` contains a nontrivial
   element supported in `c`, since the elements of `V` supported in a cone form a copy of `V`. That element is
   the identity on `C_{n+1}` but not on `C_n`, so it lies in `K_{n+1} ∖ K_n`.
3. A finitely generated subgroup of an increasing union lies in one `K_n`. Item 2 gives `K_n ≠ Stab_Γ(x)`.
4. Stabilizers of other orbit points are conjugate to `Stab_Γ(x)`, and item 3 applies to each. For
   `Γ = V`, high transitivity on the orbit is the usual cone-matching argument: every point of `V·x` has the
   form `α·σ^k(x)`, so finitely many distinct orbit points can be separated by disjoint cones and matched.
5. Apply the argument of item 1 in each coordinate. A brick replacement `(p_i w_i) ↦ (q_i w_i)` fixing `x`
   forces `|p_i| = |q_i|`, hence `p_i = q_i`, in every coordinate. Item 2's strictness uses a nontrivial element
   of `nV` supported in a sibling brick.

## Why it matters

Kourovka 7.19 (`kourovka-7-19-explicit-fp-simple-group-with-non-pr-word-problem`) and the complexity root ask for
finitely presented simple groups with hard word problems. By `twisted-brin-thompson-wp-equals-actor-orbit-problem`,
it is enough to find a type (A) actor whose point-stabilizer membership is hard.
- **The tempting move.** Let a Thompson-like group act on the orbit of a computable point `x` whose digits are
  hard to compute. Deciding `g(x) = x` would then require computing digits of `x`.
- **Why it fails.** This node shows the move never gives a type (A) action inside prefix-replacement hosts:
  finitely generated point stabilizers force the base point to be eventually periodic or singular.
- **Eventually periodic points are easy.** For them, evaluating a word at the point runs in polynomial time in
  its length.
- **Where hardness must come from.** It must be carried by the generators themselves, as in
  `hard-type-a-actors-via-hard-half-finite-shift-envelopes`, or by singular germs.
