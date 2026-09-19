---
rg: 2
id: free-group-houghton-group-is-of-type-f-infinity
kind: claim
title: The full group of the free-group tree seed (label-preserving quasi-automorphisms of the Cayley graph of F_2; calibration T0) is of type F_∞; the proof is Brown's criterion on the Farley–Hughes ball complex with a V-shaped height, whose descending links split as joins of a truncated Boolean poset and a multipartite matching complex
distinct_from:
  free-group-houghton-group-has-lopsided-descending-links: that shows the rank height fails, because lopsided vertices have disconnected descending links, and that rank − λ·min fails too; this uses the V-shaped height, under which those links become joins with a highly connected factor, and so proves T0.
  hard-evaluation-seeds-with-finitely-presented-full-groups: that poses T0 as the first non-split calibration of its condition 2; this settles T0.
---

**ESTABLISHED** (lane proof, bh-invent-03, 2026-09-19; not reviewed; no priority claimed).

**Imported inputs.**
- (I1) **Contractibility of the ball complex.** The Farley–Hughes complex `Δ` of `F`, with the ball S-structure
  and the maximal-partition scheme, is contractible (FH arXiv:2010.08035, Prop. 6.21 and Thm. 6.9). This is used as
  for Lehnert's `QV` (their Example 3.30): the domains of `Y` are the balls of its tree ultrametric. The domain check
  is not re-done here.
- (I2) **Connectivity of matching complexes.** Such complexes are highly connected when every type is abundant.
  This is the nerve lemma of FH Prop. 7.15–7.16 with the type-vector induction of Prop. 8.11. Each contracting
  vector lowers each coordinate by at most 1, so on `{all coordinates ≥ 3n+4}` the complex is `n`-connected.

**Credits.**
- T0 was posed, and FH §6.2 extracted, by bh-invent-11.
- The join split was suggested by the coordinator.
- The method is that of Brown, Farley–Hughes, and Bestvina–Brady.

## Setting

Notation is that of `free-group-houghton-group-has-lopsided-descending-links`.
- **Vertices.** Pseudovertices `v` of type `(s; n_a, n_a, n_b, n_b)` with `s = n_a + n_b − 1`.
- **Contractions.** `c_a, c_A` lower `n_b` by 1, and `c_b, c_B` lower `n_a` by 1.
- **Expansions.** Of a `b/B`-cone: `n_a + 1`. Of an `a/A`-cone: `n_b + 1`.
- **Links.** By the coupling (`𝓔`-chains must expand their bottom), the simplices of `lk(v, Δ)` are pairs
  (lower chain `P_1 ⊋ … ⊋ P_i`, upper chain `E_1 ⊊ … ⊊ E_j`) with `E_j ∩ ∪P_1 = ∅`.

**The height.** Fix `N`. Put `ℓ(v) = |n_a − N| + |n_b − N|`, and order vertices lexicographically by
`(ℓ, rank)`.
- **Tie-free:** adjacent vertices have different ranks.
- **Cocompact:** `{ℓ ≤ t}` contains finitely many types, hence finitely many `F`-orbits.
- **Descending link.** `DL(v)` is the full subcomplex of `lk(v, Δ)` on the neighbours below `v` in the `(ℓ, rank)`
  order.
- **Brown's criterion.** By (I1) and Brown's criterion in Morse form (FH Thm. 7.3), `F` is `F_n` as soon as `DL(v)`
  is `(n−1)`-connected for every `v` outside a bounded set of types.

## The four regions

Write `d_a = n_a − N` and `d_b = n_b − N`. For a lower move `P` let `α` be its number of `c_a/c_A` contractions and
`β` its number of `c_b/c_B` contractions. For an upper move `E` let `x` be its number of `b/B`-cones and `y` its
number of `a/A`-cones. By symmetry in `a ↔ b`, and since `{n_a, n_b < N}` is bounded, it suffices to treat
`n_b ≥ N`.

**Region A** (`n_a ≤ 3N/4`, `n_b ≥ N`).
- **Descending moves.** Uppers are descending iff `y < x` and `x + y < 2|d_a|`.
- **The base `D_up`.** This is the complex of descending uppers.
  - **Retraction.** `E ↦ E ∩ {b/B-cones}` is monotone, stays descending, and satisfies `f ≤ id`. So by Quillen,
    `D_up` is homotopy equivalent to the poset of nonempty `b/B`-sets of size `≤ m := 2|d_a| − 1`.
  - **Its type.** That poset is the face poset of the `(m−1)`-skeleton of a simplex, or of the whole simplex. So it is
    `(m−2)`-connected.
- **Attaching the lower vertices.** Attach the descending lower vertices `v/P` in order of increasing `|P|`. Two
  vertices of equal size are never adjacent.
  - **The current link is a join.** Every simplex through `v/P` added so far has `P` as its largest lower set. So
    the current link is exactly the join `Low_<(P) * D_up(P)`, where:
    - `Low_<(P)` is the chains of descending proper subsets of `P`;
    - `D_up(P)` is the descending uppers avoiding `∪P`.
  - **`D_up(P)` is highly connected.** The same retraction makes `D_up(P)` `(m−2)`-connected or contractible. It
    is nonempty because at least one `b/B`-cone survives `∪P`:
    - `P` uses at most `2α + β` of them;
    - `|P| ≤ 2n_a`;
    - and `2n_b > 4n_a`, or `4N − 2n_b + β > 0`.
  - **Conclusion.** Attaching cones on `(m−2)`-connected links keeps `(m−2)`-connectivity. So `DL(v)` is
    `(2|d_a| − 3)`-connected, hence `(N/2 − 3)`-connected.
  - **Lopsided and sink vertices.** These (`n_a ≤ 1`) lie here. Their obstruction disappears because the
    `b/B`-expansions now descend.

**Region S** (`3N/4 < n_a ≤ N`, `n_b ≥ N`).
- **Descending moves.** Lowers are descending iff `β ≤ α ≤ 2d_b − β`. Hence `α ≥ 1`.
- **The base `D_low`.** Its retraction `P ↦ P ∩ {c_a/c_A}` is monotone, stays descending, and satisfies
  `f ≥ id` in `Δ`'s order. So `D_low` is homotopy equivalent to the pure `c_a/c_A` matching complex, truncated at
  size `2d_b`. That complex has parts of sizes `s`, `2n_a > N`, `n_b` and `n_b`, so it is highly connected by (I2). The truncation is a skeleton of dimension `2d_b − 1`, and `d_b` is large away from
  the bounded set.
- **Attaching the uppers.** Attach the descending uppers in order of increasing `|E|`. The current link is
  `D_low(E) * Up_<(E)`, where:
  - `D_low(E)` is the descending lowers avoiding `E`;
  - `Up_<(E)` is the chains of descending proper subsets of `E`.

  `D_low(E)` is again a matching complex with parts of size at least `N/2`. Indeed `x + y < 2|d_a| < N/2`, so
  at most `N/2` cones are removed from each part.

**Region S′** (`n_a = N + 1`, `n_b ≥ N`).
- **What changes.** As in S, except that pure `c_b/c_B` sets of size `≤ 2` are also descending.
- **How they attach.** They attach with the link {descending supersets `P ⊔ Q` with `Q ⊆ c_a/c_A`}. This is a
  pure `c_a/c_A` matching complex avoiding `∪P`, hence connected.

**Region B** (`n_a, n_b ≥ N + 2`).
- **Descending moves.** No upper is descending. Every `P` with `|P| ≤ 3` is descending.
- **Reduction to `K(v)`.** Larger descending `P` attach with link {descending proper subsets}, which contains every
  subset of size `≤ 3`, so it is connected. Hence `π_1(DL(v))` is a quotient of
  `π_1(sd K(v)^{(2)}) = π_1(K(v))`, and in general `DL(v)` is as connected as `K(v)` up to the truncation.
- **`K(v)`.** Here `K(v)` is the full matching complex of the four contraction types. Its coordinates are
  `≥ N + 2`, so it is highly connected by (I2).

**Conclusion.** Given `n`, choose `N ≥ C·n` large. Every `v` outside the bounded set `{n_a, n_b < N} ∪ {ℓ ≤ L_0}`, with `L_0` large, has
an `(n−1)`-connected descending link. So `F` is of type `F_n` for every `n`, i.e. `F_∞`. ∎

## Lesson for general BH

**Multi-type seed full groups are finiteness-tame. The obstruction was the height, not the group.**
- **Rank is the wrong height.** It turns type-lopsided partitions into Houghton-like sinks.
- **The fix.** A height that rewards moving the type vector toward a far balanced centre makes the balancing
  expansions descend.
- **What the links become.** Every descending link is then a join of a truncated Boolean poset, which carries the
  balancing moves, with a multipartite matching complex. Both are highly connected.
- **For the hard-actor route (SYNTHESIS v9 #1).** Condition 2 (finite presentation) holds for the first non-split
  calibration. The same V-height template should apply to any tree seed with finitely many cone types, and plausibly
  to hierarchical seeds whose type vectors satisfy linear invariants.

## Check of Regions S and S′ (bh-invent-11, 2026-09-19, on request; internal lane check, not an external review)

**Region S: PASS.**
- **Descending conditions.** Recomputed: lowers descend iff `β ≤ α ≤ 2d_b − β`; uppers iff `y < x` and
  `x + y < 2|d_a|`.
- **The two retractions.**
  - `P ↦ P ∩ {c_a/c_A}` keeps `(α, 0)` descending, since `α ≤ 2d_b`. It satisfies `f ≥ id`.
  - When `v^E` is attached, its link is exactly `D_low(E) * Up_<(E)`. The coupling only sees the largest
    upper `E` and the largest lower `P_1`, and `E ∩ ∪P_1 = ∅` implies the condition for smaller uppers.
  - A join with a possibly empty `Up_<(E)` is at least as connected as `D_low(E)`.
- **Part sizes.** The part sizes `s, 2n_a, n_b, n_b`, and at least `N/2` after removing `E`, are correct.
- **Make explicit: the size of `L_0`.** `L_0` must depend on `N`, with `L_0 ≥ N/4 + C·n`.
  - In Region S, `d_b ≥ ℓ − N/4`, so this bound is what makes the truncation `2d_b − 2` large.
  - The row `n_b = N` (`d_b = 0`) has **no** descending lowers. It is harmless only because it lies in
    `{ℓ ≤ N/4} ⊆ {ℓ ≤ L_0}`.

**Region S′: the conclusion holds, but the description needs a repair.**
- **What is actually descending.** For `d_a = 1`, the lowers descend iff `α ≥ max(β − 2, 0)` and `α + β ≥ 1`, with
  upper bounds `α ≤ 2d_b` for `β = 0`, `α ≤ 2d_b + 1` for `β = 1`, and `α ≤ 2d_b + 2 − β` for `β ≥ 2`. This is more
  than "S plus pure `c_b` sets of size ≤ 2": for example `(α, β) = (1, 2)` and `(1, 3)` also descend.
- **No descending uppers.** For `d_a ≥ 1` every upper raises `ℓ` by `x + y`. So `DL(v)` consists of lowers only;
  the "as in S" attachment of uppers does not occur.
- **The retraction breaks at one edge case.** `P ↦ P ∩ {c_a/c_A}` fails to stay descending exactly at
  `(α, β) = (2d_b + 1, 1)`.
- **The repair.**
  1. Let `D′ = {P descending : 1 ≤ α ≤ 2d_b}`. The retraction maps `D′` into itself with `f ≥ id`, so `D′` is
     homotopy equivalent to the truncated pure `c_a/c_A` matching complex, which is highly connected by (I2).
  2. Attach the edge-case vertices `(2d_b + 1, 1)`. They have no descending proper supersets. Their link is the
     poset of proper nonempty subsets other than the single `c_b` element `{c}`. It is contractible via
     `σ ↦ σ ∖ {c}`, which is `≤ id`, onto the full simplex on `P ∖ {c}`.
  3. Attach the single `c_b` sets `{c}`. Their link is the descending supersets. The map
     `P ↦ (P ∩ c_a) ∪ {c}`, which is `≤ id`, is a homotopy equivalence onto the truncated `c_a/c_A` matching
     complex avoiding the pieces of `c`. That complex is highly connected, not merely connected as stated.
  4. Attach the pairs `{c, c′}`. Their link is `{{c}, {c′}} * (upward part)`, and the upward part is highly
     connected by the same map with `{c, c′}`.

  With this repair, Region S′ is `(n−1)`-connected for `N ≥ C·n`, and the Conclusion stands.
- **Coverage.** The cases `n_a ≥ N + 2` with `n_b ∈ {N, N + 1}` are covered by S and S′ through the `a ↔ b`
  symmetry, as the setting says.
- **Not checked here.** Regions A and B, and the imports (I1) and (I2).
