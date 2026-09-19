---
rg: 2
id: free-group-houghton-group-f-infinity-review
kind: claim
title: Referee review of the T0 proof (free-group Houghton group is F_∞) — Regions A, S, S′ and the imports pass; Region B fails near the walls min(d_a,d_b) small, so the node as written proves F_3; a repair given here (DL(v) ≃ sd of the doubly truncated matching complex) restores F_∞
distinct_from:
  free-group-houghton-group-is-of-type-f-infinity: that is the lane proof under review; this checks Regions A and B, the imports (I1), (I2) and the cutoffs, supplies the missing Region B argument, and records the literature check.
  free-group-houghton-group-fh-domain-check: that discharges (I1) by checking the Farley–Hughes hypotheses; this re-checks that check at source and also checks the Brown–Morse step and (I2).
  free-group-houghton-group-has-lopsided-descending-links: that sets up the complex and shows the rank height fails; this reviews the V-height proof that replaced it.
---

**ESTABLISHED (referee bh-ref-t0, 2026-09-19).** This is an independent review of the lane proof
`free-group-houghton-group-is-of-type-f-infinity` (bh-invent-03; landed ffbdd835bf, cc21020b55). The Region B
repair in §3 is the referee's own argument; it is **not independently reviewed**. No priority claimed.

**Statement.**
1. Region A is correct as written. The imports (I1) and (I2) are correct, with the citation repairs in §5.
2. Region B is incomplete. Its argument gives `DL(v)` connected only up to dimension `2·min(d_a, d_b) − 2`. The
   strips `n_a ∈ [N+2, N+n/2]` (and symmetrically in `n_b`) with the other coordinate large are not in the
   excluded bounded set. So the node as written proves **`F_3`** (the worst strip `d_a = 2` gives 2-connected
   descending links), not `F_∞`.
3. With the repair in §3, every descending link outside the bounded set is `(n−1)`-connected, and **T0 is of type
   `F_∞`**.

Sources read at source: Farley–Hughes, *Finiteness properties of locally defined groups*, arXiv:2010.08035v1:
Def. 3.12, Conv. 3.9, Prop. 3.24, Ex. 3.30, Def. 4.2, Ex. 4.4, Def. 4.10–4.18, Cor. 4.26, Prop. 4.27, 4.31,
Def. 6.1, 6.2, 6.6, Thm 6.9, Prop. 6.13–6.15, 6.21, Thm 7.3, Prop. 7.6, 7.14–7.16, Def. 8.7, 8.9, Prop. 8.10,
8.11, Ex. 8.12. Also Bux–Llosa Isenrich–Wu arXiv:2408.05673v2 §§1, 3, 4 and Audino–Aydel–Farley arXiv:1705.01628 §1.

## 1. Verdicts

| part | verdict |
|---|---|
| Region A | **PASS** |
| Region S | PASS (bh-invent-11's check; spot-checked here) |
| Region S′ | PASS, one harmless slip in the check (§4) |
| Region B | **FAIL as written; PASS with the repair of §3** |
| (I1) contractibility | **PASS** (citation repair for the Morse step) |
| (I2) matching complexes | **PASS with a repair**: the restricted complexes need the sub-scheme `𝓔′` (§5) |
| cutoffs `L_0 ≥ N/4 + Cn`, `N ≥ Cn` | PASS; `N ≥ 12n + 16` and `L_0 ≥ N/4 + n` suffice everywhere, including §3 |
| literature | not found as known; **credit Bux–Llosa Isenrich–Wu 2024** (§6) |

## 2. Region A (`n_a ≤ 3N/4`, `n_b ≥ N`): PASS

- **Descending sets.** With `d_a ≤ −N/4 < 0 ≤ d_b`: an upper `E` descends iff `ℓ` strictly drops, i.e.
  `|d_a + x| + y < |d_a|`, which is equivalent to `y < x` and `x + y < 2|d_a|`. A lower `P` descends iff
  `ℓ` does not rise (its rank drops), i.e. `β + |d_b − α| ≤ d_b`, which is equivalent to `β ≤ α ≤ 2d_b − β`.
  Both match the node.
- **The base.** Every chain of uppers is a simplex, so `D_up` is the order complex of the descending `E`. The map
  `E ↦ E ∩ {b/B}` is monotone, `≤ id`, and lands in `{1 ≤ x ≤ m}`, `m = 2|d_a| − 1`. Its image is the face poset of
  the `(m−1)`-skeleton of the simplex on the `2n_b > m` cones, so `D_up` is `(m−2)`-connected.
- **Attaching lowers by increasing `|P|`.** Equal-size lowers are incomparable. When `v/P` is added, `P` is the
  bottom vertex of every simplex through it, and the coupling `E_top ∩ ∪P = ∅` is checked only against `P`. So
  the link is exactly `Low_<(P) * D_up(P)`. The same retraction makes `D_up(P)` a full simplex or an
  `(m−2)`-connected skeleton, as soon as one `b/B`-cone avoids `∪P`.
- **Survival.** `P` uses `2α + β` of the `b/B`-cones and `α + 2β ≤ 2n_a` of the `a/A`-cones. So
  `2α + β ≤ min(4d_b, 4n_a)`. If `4n_a ≥ 2n_b`, then `n_b ≤ 3N/2`, and `4d_b ≤ 2n_b − N < 2n_b`. At least `N` cones
  always survive. (The node's sentence is garbled but its content is right.)
- **Conclusion.** `DL(v)` is `(2|d_a| − 3)`-connected, hence `(N/2 − 3)`-connected, with no condition on `d_b`.

## 3. Region B (`n_a, n_b ≥ N+2`): the gap and a repair

**The gap.**
- For `d_a, d_b ≥ 1` no upper descends, and a lower `(α, β)` descends iff `g_a(β) + g_b(α) ≤ 0`, where
  `g_d(t) = |d − t| − d = max(−t, t − 2d)`.
- The node uses "every `P` with `|P| ≤ 3` descends". This gives `π_1` correctly, but for higher connectivity only
  the faces of size `≤ R = 2·min(d_a, d_b)` are all descending.
- The Boolean attaching lemma (a subposet of `B_k ∖ {top}` containing all sets of size `≤ r+1` is `(r−1)`-connected,
  by induction on size) then gives `DL(v)` only `min(conn K(v), R − 2)`-connected.
- At `d_a = 2`, `d_b → ∞` this is 2. Those vertices have `ℓ → ∞`, outside `{n_a, n_b < N} ∪ {ℓ ≤ L_0}`.

**Repair Lemma (referee, not independently reviewed).** For every vertex with `d_a, d_b ≥ 1`,
`DL(v) ≃ sd K_0(v)`, where `K_0(v) = {P ∈ K(v) : α_P ≤ 2d_b, β_P ≤ 2d_a}`. Moreover, if `n ≥ 1`,
`N ≥ 4n + 4` and `max(d_a, d_b) ≥ (n+1)/2`, then `K_0(v)` is `(n−1)`-connected.

*Proof.*
1. **Overshoots are contractible attachments.** A descending `P` not in `K_0` overshoots exactly one
   coordinate, say `α_P = 2d_b + t` with `1 ≤ t ≤ d_a`, and then `t ≤ β_P ≤ 2d_a − t`; β-overshoots are symmetric.
   - Its descending proper subsets with `α ≤ 2d_b` are all `Q ⊊ P` with `|Q ∩ A_P| ≤ 2d_b`. That is the face poset
     of the join (skeleton of the simplex on `A_P`) `*` (full simplex on `B_P`). Since `B_P ≠ ∅`, it is contractible.
   - The remaining descending proper subsets are smaller overshoots of the same kind. A proper subset of an
     α-overshoot has `β ≤ β_P < 2d_a`, so it is never a β-overshoot (and symmetrically).
   - By induction on size, each is attached along a contractible link, so the poset of descending proper subsets
     of `P` is contractible.
   - Now attach the overshoots to `K_0` in increasing size. Their supersets are not yet present (a superset of
     an α-overshoot is an α-overshoot or not descending), so each link is that contractible poset. So
     `DL(v) ≃ sd K_0(v)`.
2. **If `min(d_a, d_b) ≥ (n+1)/2`**, `K_0(v) ⊇ K(v)^{(n)}`. `K(v)` is `n`-connected by (I2), since every coordinate
   is `≥ N ≥ 3n+4`. A complex between the `n`-skeleton and `K(v)` is `(n−1)`-connected, by cellular approximation.
3. **If `d_a = k ≤ n/2`** (the other case is symmetric), write `K_0(u; A, B)` for the faces of `K(u)` with
   `α ≤ A` and `β ≤ B`. We show by induction on `B` that it is `c`-connected, where
   `c = min(conn K_a(u′), A − 2)` over the pseudovertices `u′ = u − (≤ B contracting sets)`, and `K_a` is the pure
   `c_a/c_A` complex.
   - **The `α ≥ 1` faces.** `P ↦ P ∩ {c_a/c_A}` is monotone and `≤ id`. It retracts these faces onto
     `sd K_a(u)^{(A−1)}`.
   - **The pure-β faces.** Attach them (`1 ≤ β ≤ B`) in *decreasing* size. The link of such a `P` is the poset of
     its present supersets, which is isomorphic to the face poset of `K_0(u − ∪P; A, B − β_P)`. That is
     `c`-connected by induction.
   - For `u = v`, `A = 2d_b`, `B = 2k`: each `u′` lies below `v` by at most `n` contracting sets, so every coordinate is
     `≥ N − n ≥ 3(n−1) + 4`. So `K_a(u′)` is `(n−1)`-connected by (I2) applied to `𝓔′` (§5), and
     `2d_b − 2 ≥ n − 1`. ∎

**Use.** For `ℓ(v) > L_0 ≥ N/4 + n` and `min(d_a, d_b) ≤ n/2`, the other coordinate is `≥ L_0 − n/2 ≥ (n+1)/2`, which suffices.
So every Region B vertex outside the bounded set has an `(n−1)`-connected descending link.
- The lemma also re-proves Region S′ (`k = 1`). There the overshoots are the `(2d_b+1, 1)` edge cases and the
  `(α, β ≥ 3)` sets, and the pure-β faces are the single `c_b` sets and their pairs, as in bh-invent-11's check.

## 4. Region S′: bh-invent-11's check has one harmless slip

- **Step 2.** The link of an edge case `P = (2d_b+1, 1)`, with `c` its `c_b` set, excludes `{c}` **and**
  `A_P = P ∖ {c}`, since `(2d_b+1, 0)` does not descend.
- **So it is a sphere.** It is `≃ S^{2d_b−1}` via `σ ↦ σ ∪ {c}` onto the proper faces of the simplex on `A_P`. It is
  not contractible as stated.
- **Harmless.** A `(2d_b−2)`-connected link suffices, so the conclusion is unchanged.
- **Steps 3–4 are correct.** The pair link is the suspension `{{c},{c′}} * U`.

## 5. The imports and the cutoffs

**(I1) contractibility: PASS.** The domain-check node's four items hold at source:
- **Compact ultrametric property (FH Def. 3.12).** Cones meet only when nested, and the complement of a cone or of
  a point is a finite union of domains.
- **Maximal `S`-structure (FH Ex. 4.4).** `𝕊(C^0(v), C^0(w)) = {w v^{-1}}` when the last letters agree, and `∅`
  otherwise, since a translation carries the apex to the apex. So there are five domain types and every `𝕊(D,D)`
  is trivial.
- **Conv. 3.9.** `X = {o} ⊔` the four cones.
- **Contractibility.** FH Prop. 6.21 then makes the maximal-partition scheme `n`-connected for all `n`, and Thm 6.9
  makes `Δ^𝓔` contractible.

Two more facts the proof uses also hold:
- **The type vectors.** Every vertex has type `(n_a+n_b−1; n_a, n_a, n_b, n_b)`. By Cor. 4.26 any vertex and the
  root have a common expansion. The relation lattice, spanned by `(1;0,0,1,1)` and `(1;1,1,0,0)`, is saturated in
  `Z^5`.
- **The group.** `Γ_S ≅ F`: image pieces containing `o` split into finitely many cones away from `o`.

*Citation repair.* FH Thm 7.3 is Brown's criterion for a filtration, not a Morse form. The filtration is by the full
subcomplexes `{ℓ ≤ k}`, and those vertices are added in rank order.
- **Tie-free.** Each `(ℓ, rank)` value class is an antichain, since adjacent vertices differ in rank.
- **The Morse step.** Adding vertices along `(n−1)`-connected descending links is the Bestvina–Brady Morse lemma,
  the analogue of FH Prop. 7.6.
- **Cocompactness.** `{ℓ ≤ k}` is an invariant subcomplex of a rank-bounded `Δ_r`, which is cocompact by FH
  Prop. 6.13.
- **Stabilizers.** They are finite, by Prop. 5.3 and Cor. 6.15.

**(I2) matching complexes: PASS with a repair.**
- **The arithmetic.** Region `{all coordinates ≥ 3n+4}` checks against FH Prop. 8.11:
  - `α_n − 1 ≥ α_(n−1)`;
  - `α_n − j ≥ α_(n−j+1)` iff `2j ≥ 3`;
  - `α_(−1) = 1` supplies the nonempty `lk↓` that Prop. 7.16 silently needs.
- **What needs saying.** FH §§7.4–8.2 compute `lk↓` for the scheme's own contracting vectors. The node applies
  (I2) to the **pure `c_a/c_A`** complexes, and it must say why. They are the `lk↓` of the sub-scheme `𝓔′`, which
  expands only `a`/`A`-cones.
  - `𝓔′` satisfies Def. 6.1(1)–(4): it is invariant because the domain type is.
  - FH 7.14–7.16 and 8.11 hold for any expansion scheme. The `n`-connectedness of `𝓔′` is never needed.
- **Truncations.** Truncating at size `m` is an `(m−1)`-skeleton, so the connectivity is `min(conn, m−2)`.
- **Region S's `D_low(E)`.** Removing `E` can drop the single `a`-coordinate to `N/4`, not to `N/2`. So the
  needed bound is `N/4 ≥ 3n + 4`, which `N ≥ 12n + 16` gives.

**Cutoffs.**
- **Region S.** `L_0 ≥ N/4 + Cn` is right, since `d_b ≥ ℓ − N/4` there.
- **Region A.** No cutoff is needed.
- **Region B and S′.** The same `L_0` works by §3.

## 6. Literature (priority is not a risk; credit generously)

No source found that proves T0 finitely presented or `F_∞`. Must be credited:
- **Bux–Llosa Isenrich–Wu**, *On the Boone–Higman Conjecture for groups acting on locally finite trees*,
  arXiv:2408.05673v2.
  - **T0 is their group.** In their notation T0 is `RP_{F_2}(C(F_2,{a,b}))`. Their Remark 1.6 identifies such groups
    with the quasi-automorphism groups of the directed labeled Cayley graph. Their Example 1.5 notes that they are in
    general not finitely presented (`G = Z` gives `H_2`).
  - **Their theorem does not cover T0.** Their Prop. 9.2 (`RP_G(T)` is `F_n` when edge stabilizers are `F_n`) assumes
    the viral expansion property, Def. 4.3: `M_ii ≥ 3` and `L_i(T_0) ≥ 2`. On the rose `Γ = F_2∖T`, the only
    admissible gate system is all four half-edges (loops need both). Each caret is then a star with **one** terminal
    leaf of its own type, so `M_ii = 1`.
  - **So T0 is a non-viral case outside their theorem.** The V-shaped height is exactly what replaces viral
    expansion. Their Stein–Farley and Morse method is the closest precedent.
- **Audino–Aydel–Farley** (AGT 2018; arXiv:1705.01628) prove `QV` is `F_∞`. They say their argument "extends with
  equal ease" to finitely many binary trees and isolated vertices, and to `n`-ary trees. They say it "likely"
  extends to non-regular trees, which they leave speculative.
- **Farley–Hughes Ex. 8.12** (`QV` via Prop. 8.11) is the template the proof follows.
- **Related work.**
  - Nucinkis–St. John-Green (2018), on finiteness of `QF`, `Q̄T`, `Q̄V`.
  - D'Angeli–Matucci–Perego–Rodaro, arXiv:2408.13070: transition groups of context-free graphs, with no finiteness
    results.
  - Lehnert's thesis (Frankfurt 2008), cited by Bux–Llosa Isenrich–Wu for quasi-automorphism groups. **Not
    checked; not accessible here.**

## 7. What T0 being `F_∞` buys (SYNTHESIS v9.1, 10522354c, top-problems row 1)

- **What row 1 asks.** Row 1, HARD-(A) in seed form, needs the plain full group `[[Γ ⋉ Y]]` fp with a fg seed
  stabilizer. It names "first test the Houghton group of the free group", which is T0.
- **What it gives.** With the §3 repair, the finiteness half passes for the first multi-type, non-split tree seed.
  The Houghton-type lopsidedness is an artifact of the rank height, not an obstruction of the group.
- **What it does not give.** It does not give HARD-(A):
  - T0's seed (geodesic-to-origin) is easy to evaluate.
  - Finite generation of the seed stabilizer (`o` fixed) is not addressed. The same proof on `Δ^𝓔(PV_{X∖{o}})`
    (FH Thm 6.9 covers `PV_Y`) plausibly gives it; not checked.
  - The hard part, a hierarchical hard-to-evaluate seed whose full group stays fp, is untouched.
  - bh-invent-03's later nodes (5a0acf2cc9, c036004d94) argue that finite-type FH structures force finite-state
    generators. If that is right, this engine can reach HARD-(A) only through non-finite-state structure groups.
    Those nodes are under separate review.

## Lesson for general BH

- **A far balanced centre can stand in for viral expansion.** Stein–Farley finiteness proofs for rigid-permutation
  or full groups on trees need viral expansion (Bux–Llosa Isenrich–Wu) or richness (Farley–Hughes 2015). Both fail
  when some cone type reproduces itself fewer than three times. A V-shaped height toward a far balanced centre
  replaces that hypothesis.
- **The walls are where such proofs break.** The proof must handle the walls `d_a = 1, 2, …` of the V separately,
  and there the descending link is a doubly truncated matching complex. These strips are exactly what the first
  write-up missed.
