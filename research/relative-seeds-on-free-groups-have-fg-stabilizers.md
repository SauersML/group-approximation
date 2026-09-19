---
rg: 2
id: relative-seeds-on-free-groups-have-fg-stabilizers
kind: claim
title: Seed-forced points over a free group are finite-state and forced at linear radius, so a relative seed on a free vertex group has a finitely generated stabilizer with regular membership; the Higman-Clapham rope can never be relative-seeded on its free vertex group, and a machine-simulating seed tower must carry its machine on a distorted edge of a vertex group that is not free
distinct_from:
  relative-seeds-glue-graphs-of-groups-into-class-c: that glues relative seeds, and supplies them for finitely generated edge groups of free and free abelian vertex groups; this proves that over a free vertex group no other relative seeds exist.
  higman-clapham-towers-leave-the-seed-form-at-three-steps: that locates the three steps where the tower leaves the seed form and asks whether gluing allows infinitely generated edge groups (the rope, step 3); this answers no for free vertex groups.
  seed-collapse-is-bounded-by-forcing-radius-and-dehn: that bounds certified complexity by forcing radius and Dehn function in general; this computes both for free groups (linear, linear), where nothing hard can live.
---

**ESTABLISHED (lane proof, bh-g1-universal-point, 2026-09-18; elementary, not independently reviewed).** This is
work for the SEED TOWER team, on the target "a seeded tower over distorted edges that simulates a machine".

**Setting.**
- `F` is free on a basis `S`, so its Cayley graph is a tree `T`.
- The action is `(λ·x)(h) = x(λ⁻¹h)`, and rules read `x` at `h` and `hu` for `u ∈ U = Ball(u_0)`.
- A *(relative) seed* is an SFT `Y` with a pattern `p` on `Ball(c_p)` such that `[p] ∩ Y = {y}`. For a relative
  seed, `C = Stab(y)` may be nontrivial. This matches `relative-seeds-glue-graphs-of-groups-into-class-c`.

## Theorem

1. **Finite-state.**
   - Let `e` be an edge at distance `> c_p + 2u_0` from `1`, and `T_far(e)` the side of `e` away from `1`.
   - Then `y|T_far(e)` is determined by the last letter of `e` and the pattern of `y` on the `2u_0`-neighbourhood
     `W_e` of `e`, read relative to `e`.
   - So there are finitely many subtree types, and `y` is computed by a finite automaton reading reduced words.
2. **Linear forcing.** There is `c` such that every pattern on `Ball(n + c)` that obeys the rules and has `p` at
   `1` agrees with `y` on `Ball(n)`.
3. **Stabilizers.** `C = Stab(y)` is a rational subset of `F`. Hence it is finitely generated (Anisimov–Seifert,
   recalled), and membership in `C` is decided by a finite automaton on reduced words.

## Proof

**Splicing.**
- Let `y_1, y_2 ∈ Y` agree on `W_e`. A rule window meeting both sides of `e` has radius `u_0` and centre within
  `u_0` of `e`, so it lies inside `W_e`.
- Hence the splice (`y_1` on the near side, `y_2` on `T_far(e)`) is in `Y`.
- If the seed ball lies on the near side and `y_1 = y`, the splice is in `[p] ∩ Y = {y}`. So `y_2 = y` on
  `T_far(e)`.

**Part 1.**
- Let `e`, `e'` end at `g`, `g'` with the same last letter `s`, and let their `W`-patterns agree relative to
  `g, g'`.
- Put `λ = g'g⁻¹`. Left multiplication by `λ` maps `T_far(e)` onto `T_far(e')`, by `gw ↦ g'w` for reduced `w` not
  starting with `s⁻¹`.
- Then `y_2 = λ·y ∈ Y` agrees with `y` on `W_{e'}`. Splicing at `e'` gives `y(g'w) = y(gw)` on `T_far(e')`.
- The type of a child edge is read off the parent's type, since `W_child ⊆ W_e ∪ T_far(e)`.

**Part 2.**
- A boundary pattern at `e` is *live* if it extends to a valid configuration on `W_e ∪ T_far(e)`. Liveness at
  depth `j` is decided by the finite type system.
- The sets of patterns valid to depth `j` decrease and stabilize after at most `N` steps, where `N` is the number
  of boundary patterns.
- A pattern on `Ball(n + c)`, with `c = c_p + 2u_0 + N`, that obeys the rules has only live boundary patterns at
  depth `≤ n + c_p + 2u_0`.
- Compactness then extends it to a point of `[p] ∩ Y = {y}` on each branch separately, since the branches of a
  tree are independent across the cut windows.

**Part 3.**
- `λ ∈ C` iff `λ·y ∈ [p]`, iff `y(λ⁻¹h) = p(h)` for `h ∈ Ball(c_p)`.
- By Part 1, the pattern of `y` at a reduced word `g` is a finite-state function of `g`. It depends on the types
  of its last `c_p` prefixes and on the fixed initial ball.
- So `{g : pattern at g = p} = C⁻¹ = C` is a regular language of reduced words, hence a rational subset. ∎

**Remark (virtually free groups).** The same splicing works for any context-free group, across the bounded cut sets
of Muller–Schupp cone types. This is a sketch only; the node claims just the free case.

## Consequences for the seed tower

- **(a) The rope is excluded.** Aanderaa–Cohen step 3 and Clapham's Lemmas 9.2/11.2 need an HNN over an infinitely
  generated free factor `⟨t_α : α ∈ I⟩` of a free vertex group.
  - By Part 3, no relative seed on that free vertex group has this stabilizer.
  - So the relative-seed gluing cannot perform the rope as written. This answers bh-invent-14's ask: **no, not
    over free vertex groups**.
  - The rope must either be re-routed through a vertex group that is not free, or be replaced by a finitely
    generated distorted edge.
- **(b) Free vertex groups carry no machine.** Their relative-seed edges are finitely generated, hence
  quasiconvex and undistorted. Membership in them is regular.
  - By `bi-lipschitz-splittings-add-one-exponential-to-the-word-problem`, such an edge costs at most one
    exponential.
  - Seeds on `F` itself have linear forcing radius and linear Dehn function. So in the sandwich of
    `seed-collapse-is-bounded-by-forcing-radius-and-dehn` their certified complexity is at most `2^{O(n)}`.
- **(c) Undistorted edges are never the machine, even with hard vertex groups.** Suppose a finitely generated
  undistorted edge group `C ≤ A` has undistortion constant `L`.
  - Membership `g ∈ C` is decided by trying all `C`-words of length `≤ L|g|`, in time `2^{O(|g|)}·T_A(O(|g|))`.
  - So hypothesis (M) of the bi-Lipschitz node is automatic at the cost of one exponential.
  - Hence both hypotheses of that node reduce to distortion alone. The claim "distortion is the currency" is exact.
- **(d) Where the machine must sit.** The machine of a CAP-refuting tower needs:
  - a vertex group `A` that is not virtually free, since free groups are excluded by (a) and (b);
  - an edge `C ≤ A` with non-elementary distortion, by (c);
  - a rigid relative seed for `(A, C)`, whose forcing radius carries the machine by the sandwich.

  This is exactly Clapham–Cohen step 4, `(H_2, A_+)`, which the bh-invent-14 map marks "relative seeds are hard".

**Simplest test case.** A Mikhailova fibre product `M_Q ≤ F × F` for a finitely presented `Q`.
- It is finitely generated and distorted, and membership in it is `WP(Q)`.
- A relative seed for `(F×F, M_Q)` has an orbit that is `Q` under the left-right action: right cosets `M_Q(u,v)`
  correspond to `π(u)⁻¹π(v)`.
- The obstacle is visible. Local rules can impose `y(h(r,1)) = y(h)` for relators `r`, but not for their
  conjugates. So the seed itself must force invariance under the normal closure, and that is a seed statement for
  `Q`.
- Whether seeded `Q` gives a relative seed for `(F×F, M_Q)` is the open rung. A yes would carry `WP(Q)` into a
  seeded tower through a single edge.

## Lesson for general BH

- **Free geometry forbids computation in seeds.** Trees split along edges, so a seed over a free group is
  finite-state. Its relative seeds have finitely generated, regular, undistorted stabilizers.
- **So the tower's machine can live neither in the rope nor in any free vertex group.**
- **Together with the bi-Lipschitz bound, the target is pinned down.** Because undistorted edges also have
  membership at one exponential, a seed tower that refutes CAP needs three things:
  - a non-free vertex group;
  - a non-elementarily distorted edge;
  - a rigid relative seed that forces the distorted coset structure.

  Clapham–Cohen's step 4 and Mikhailova fibre products are the two concrete places to try.

## Referee (bh-ref-kourovka-b, 2026-09-18): PASS

**Verdict: PASS** for Parts 1–3 and for consequences (a) and (c). Lane bh-g1-universal-point's
splicing argument is correct. It agrees with item 3 of
`sft-isolated-points-are-finite-state-across-finite-edge-groups` (bh-g3-topfree), which extends it to
virtually free groups.
- **Splicing.** A rule window meeting both sides of `e` contains `e`, so it lies in `W_e`. The seed
  ball is on the near side.
- **Part 1.** `λ = g'g^{-1}` carries `T_far(e)` onto `T_far(e')`, and `λ·y ∈ Y` agrees with `y` on
  `W_{e'}`. Child types are read off the parent's type.
- **Part 2.** The depth-`j` validity sets decrease and are updated by a fixed monotone map, so they
  stabilize in `≤ N` steps. König plus branch independence then gives the linear forcing radius.
  The constant `c` may need an extra `2u_0`, but only its existence is claimed.
- **Part 3.** `C^{-1} = C` is the regular set of reduced `g` with `y(g·) = p`, so it is rational and,
  by Anisimov–Seifert, finitely generated. Correct.
- **Consequences.**
  - (a) The rope's infinitely generated free factor cannot be a relative-seed stabilizer. Correct.
  - (c) The `2^{O(|g|)}·T_A` membership bound for undistorted edges is correct.
  - (b) and (d) rest on the cited bi-Lipschitz and sandwich nodes, which I did not re-referee.
- **Mikhailova remark.** The coset invariant `π(v)^{-1}π(u)` is correct.
