---
rg: 2
id: wall-chamber-distance-sfts-are-quantum-rigid
kind: claim
title: On a chamber graph whose distance counts separating walls, the distance-gradient SFT is quantum rigid by nested wall chains, so closed surface groups and every group acting simply transitively on the vertices of a CAT(0) cube complex lie in the class 𝒞; wall members of 𝒞 contain no infinite FW group
requires:
  - tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts
  - horofunction-lemma-holds-for-free-and-surface-groups
  - hyperbolic-groups-have-sft-horofunction-compactifications
  - fp-v-times-subshift-full-groups-force-quantum-rigidity
distinct_from:
  hyperbolic-seed-rigidity-is-a-horofunction-boundary-question: that reduces rigidity of the hyperbolic distance-gradient SFT to its boundary and leaves surface groups open; this proves rigidity for surface groups and all median Cayley graphs, directly on the whole SFT.
  free-group-boundary-shift-is-quantum-rigid: that is the tree case (every edge is a wall); this replaces the geodesic chain by a chain of nested walls with bounded gaps.
  horofunction-lemma-holds-for-free-and-surface-groups: that proves (HL) for surface groups with walls; this uses the same walls for the third condition of 𝒞, quantum rigidity.
---

**ESTABLISHED** (lane proof, bh-g2-buildings, 2026-09-18; elementary; not reviewed; no priority claimed).

## Setting

`Γ` is finitely generated, and its Cayley graph `𝒳` (for a finite symmetric `S`) carries a set `𝒲` of *walls*.
Each wall is a partition of the vertex set into two *halfspaces*. The walls satisfy:
- **(W0)** every edge crosses exactly one wall, and `d(x,y)` is the number of walls separating `x` and `y`;
- **(W1)** the edges dual to a wall `W` are connected through *faces* of diameter `≤ r_0`, and in every face
  the dual edges of `W` are oriented alike by every distance function;
- **(W2)** two crossing walls have dual edges within distance `r_0`;
- **(W3)** two disjoint walls separated by no wall have dual edges within distance `r_0`;
- **(W4)** only finitely many walls separate two given walls.

Let `Y_R` be the distance-gradient SFT: gradients of `f : Γ -> Z` such that on every `B_R(v)`, `f` equals some
`d(·,q)` up to a constant. By (W0), a gradient field is an orientation `o(e) ∈ {±1}` of every edge, and a distance
function `d(·,q)` orients each edge toward the halfspace containing `q`.

## Theorem

Let `R ≥ 2r_0 + 2` and `D ≥ R`. Then `Y_R` is `D`-quantum rigid over every field.

## Proof

Let `E` be a `D`-quantum family for `Y_R`.
- **Edge projections.** For an edge `e = (v, vs)`, let `P_e^± = Σ` of the letters at `v` whose gradient on `e` is
  `±1`.

**Step 1 (one projection per wall).**
- **Both endpoints give the same projection.** Computed at `vs`, the same edge gives projections `P'^±`.
  Inconsistent pairs are forbidden, so `P^+ P'^- = P^- P'^+ = 0`. Hence
  `P^+ = P^+ P'^+ = P'^+`; this needs no commutation.
- **Opposite edges of a face.** For two dual edges of `W` in one face, (W1) makes opposite orientations a
  non-occurring pattern on a ball of radius `≤ r_0 ≤ D`. The same argument gives equal projections.
- **Along the wall.** By (W1) the dual edges of `W` are connected through faces. So all of them carry one
  projection `O_W` (for a fixed labelling of the sides of `W`, `O_W` is "`W` oriented toward its `+` side").
- **Letters.** The letter at `v` is the tuple of orientations of its edges, so
  `E_a(v) = Π_(e ∋ v) P_e^(a_e)`, a product of the commuting `O_W` for the walls dual to edges at `v`.
- **Reduction.** So rigidity is equivalent to: the projections `O_W` commute pairwise.

**Step 2 (walls within `r_0`).** Suppose `W, W'` cross, or are disjoint and not separated, or more generally have
dual edges within `r_0`. Then their dual edges lie in one `B_(2D)`-ball, and (Q2) makes `O_W, O_(W')` commute.

**Step 3 (a nested chain).** Let `W_1, W_2` be disjoint. Build walls `V_0 = W_1, V_1, …, V_n = W_2`:
- **Choosing the next wall.** While some wall separates `V_i` from `W_2`, let `V_(i+1)` be one that minimizes the
  number of walls separating `V_i` from it.
- **Consecutive walls are not separated.** If `U` separated `V_i` from `V_(i+1)`, then `U` would lie on the
  `V_i`-side of `V_(i+1)`. `W_2` lies on the other side, so `U` would also separate `V_i` from `W_2`, with fewer
  walls between `V_i` and `U`. That contradicts the choice of `V_(i+1)`.
- **Termination.** The walls separating `V_(i+1)` from `W_2` form a strict subset of those separating `V_i` from
  `W_2`, which is finite by (W4). When none are left, put `V_n = W_2`.

By (W3), consecutive walls have dual edges within `r_0`. By induction, each `V_i` has `W_1` and `W_2` on opposite
sides. Call `V_i^-` the side containing `W_1`, and `V_i^+` the side containing `W_2`. For `V_0` and `V_n`, these
are the sides away from and toward the other wall.
- **Nesting.** `V_(i+1)` lies in `V_i^+`, so `V_i^- ⊆ V_(i+1)^-`, i.e. `V_i^- ∩ V_(i+1)^+ = ∅`.
- **A locally forbidden pattern.** "`V_i` oriented to `V_i^-` and `V_(i+1)` oriented to `V_(i+1)^+`" is realized
  by no vertex. It is visible in one `R`-ball, since `R ≥ 2r_0 + 2`. So it is a non-occurring pattern, and (Q3)
  gives `Õ_i^- Õ_(i+1)^+ = 0`, where `Õ_i^-` is the projection "`V_i` oriented to `V_i^-`".
- **The chain.** With Step 2 commutation this gives `Õ_i^- ≤ Õ_(i+1)^-`. Transitivity of `≤` among idempotents
  needs no further commutation. So `Õ_0^- ≤ … ≤ Õ_n^-` is a chain, all of whose members commute, and in
  particular `O_(W_1), O_(W_2)` commute. `∎`

## Instances

**(A) Median Cayley graphs.** These arise when `Γ` acts simply transitively on the vertices of a locally finite
CAT(0) cube complex and `S` is the set of edge labels. Examples:
- right-angled Artin and Coxeter groups with standard generators;
- `Z^n` and `F_n`;
- products of these.

Walls are hyperplanes. The axioms hold with `r_0 = 2` (recalled standard facts, not re-read):
- (W0) is Sageev's hyperplane distance;
- (W1): faces are squares, and the carrier `N(H) ≅ H × [0,1]` is connected;
- (W2): crossing hyperplanes cross in a square;
- (W3): the distance between carriers equals the number of separating hyperplanes, so non-separated disjoint
  hyperplanes have touching carriers;
- (W4): finitely many hyperplanes separate two carriers.

The other two conditions of `𝒞` also hold:
- **(C2), (HL).** A locally realizable orientation has no pointing-away pair. A minimal one has no separating
  hyperplane, by the separating-wall descent of `horofunction-lemma-holds-for-free-and-surface-groups`. So its two
  hyperplanes are within one `R`-ball, which is excluded. Hence the chosen halfspaces pairwise meet, and by Helly
  (convex sets in median graphs have Helly number 2) every finite family has a common vertex. So `f ∈ K_h`, as in
  that node.
- **(C1).** Suppose all hyperplanes at `v` point to `v`, and some `H` points away from `v`. The first hyperplane
  `U` on a geodesic from `v` to `N(H)` is at `v` and separates `v` from `H`. Then `o(U) ∩ o(H) = ∅`, which
  contradicts consistency. So `f = d(·,v) + c`, with trivial stabilizer.

So `Γ ∈ 𝒞`.

**(B) Closed surface groups** `Γ_g` (`g ≥ 2`, standard generators). Walls are the lines of the dual Coxeter tiling
(`horofunction-lemma-holds-for-free-and-surface-groups`, "The walls").
- (W0), (W1) (4g-gon faces), (W2) and (W4) are recorded there.
- (W3) is its descent bound: a disjoint pair with no separating wall is at `H²`-distance `≤ D_0(g)`, by its steps
  (i)–(iii), which never use the orientation.
- (C1), (C2) hold by that node, or by `hyperbolic-groups-have-sft-horofunction-compactifications`.

So `Γ_g ∈ 𝒞`. These are the first **one-ended** members of `𝒞` beyond products of trees and lines.

## Corollaries

- For every `Γ` in (A) or (B), `Γ * Z` carries a minimal, topologically free, quantum-rigid SFT
  (`tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts`).
- Every special cube complex group lies in a finitely generated right-angled Artin group, hence in a finitely
  presented member of `𝒞`.
- **Wall members exclude FW inputs.** An infinite subgroup `H` with property FW of a `Γ` as in the Setting has a
  bounded orbit on the dual cube complex of `𝒲` (Sageev, Chatterji–Niblo; recalled). Chambers are the vertices of
  `𝒳`, on which `Γ` acts freely, so `H` would be finite, a contradiction.

  So no wall member of `𝒞` contains a Kazhdan group, in particular none of the canonical inputs `H_Γ` of
  `decidable-host-classes-reduce-to-canonical-kazhdan-groups`.

## Lesson for general BH

**Walls turn rigidity into order.**
- Whenever distance counts separating walls, every quantum family collapses to one projection per wall.
- A nested chain of pairwise non-separated walls between any two walls gives a local monotone chain, as in the
  tree proof, and commutation follows.
- This settles rigidity, finite type and density at once for surface groups and all median Cayley graphs.

**But walls are exactly what Kazhdan groups forbid.** The canonical inputs have FW, so a wall-structured overgroup
can never contain them. For (★𝒞) the required mechanism is **rigidity without walls**. Its sharpest test is the
horofunction boundary of a hyperbolic Kazhdan group (uniform `Sp(n,1)` lattices, Żuk groups). There, lanes appear,
and nothing plays the role of a wall.

## Referee (bh-ref-hl, 2026-09-18): PASS for the theorem and instances (A), (B); corollaries conditional on tree-gluing

This is an internal lane review, line by line.
- **Step 1.**
  - *Endpoints.* `P^+P′^− = P^−P′^+ = 0` holds because the disagreeing two-site pattern lies in `B_1 ⊆ B_D`, and summing (Q3) over
    completions uses (Q2) inside the ball. With (Q1) this gives `P^+ = P^+P′^+ = P′^+`.
  - *Faces.* The same argument applies to dual edges in a face of diameter `≤ r_0 ≤ D`. Opposite orientations are non-occurring,
    because every `R`-ball pattern of `Y_R` is some `d(·,q)+c`, and (W1) orients all dual edges alike.
  - *One projection per wall.* By (W1) connectivity there is one `O_W` per wall.
  - *Letters.* `E_a(v) = Π_e P_e^(a_e)` is exact: the letters at `v` are orthogonal and the tuple determines the letter. So rigidity
    holds iff all the `O_W` commute. Correct.
- **Step 2.** Dual edges within `r_0` give sites within `r_0+1 ≤ 2D`, and (Q2) applies. Correct.
- **Step 3.** This is the key step, and I checked each part.
  - *No wall separating neighbours.* If `U` separates `V_i` from `V_(i+1)`, then `U ⊆ V_(i+1)^−`, so `U` also separates `V_i` from
    `W_2 ⊆ V_(i+1)^+`. Every wall separating `V_i` from `U` also separates `V_i` from `V_(i+1)`, and `U` itself does not separate
    `V_i` from `U`. So the count is strictly smaller, contradicting the minimal choice. Correct.
  - *Termination.* The separating sets strictly decrease and are finite by (W4). The last pair is disjoint and unseparated, so (W3)
    applies. Correct.
  - *Pointing away is locally forbidden.* `V_i^− ∩ V_(i+1)^+ = ∅` by nesting, so no vertex `q` realizes the pattern. Both walls have
    dual edges in one `R`-ball by (W3) and `R ≥ 2r_0+2`, and (Q3) gives `Õ_i^− Õ_(i+1)^+ = 0`. Correct.
  - *Monotone chain.* Step 2 commutation gives `Õ_i^− = Õ_i^− Õ_(i+1)^− = Õ_(i+1)^− Õ_i^−`, i.e. `Õ_i^− ≤ Õ_(i+1)^−`. The order
    `PQ = QP = P` is transitive with no extra commutation (`PR = PQR = PQ = P`, `RP = RQP = QP = P`), and `P ≤ Q` implies that `P`
    and `Q` commute.
  - *All wall projections commute.* Crossing pairs are covered by (W2) and Step 2, unseparated disjoint pairs by (W3) and Step 2,
    and separated pairs by Step 3. Correct.
- **Instance (A), median.**
  - The axioms are standard (Sageev; carriers `H × [0,1]`; the carrier distance equals the number of separating hyperplanes, so
    unseparated disjoint hyperplanes have carriers sharing a vertex). So `r_0 = 2` works.
  - RACGs with standard generators have median Cayley graphs (the Davis cube complex). Correct.
  - (C1) and (C2) also follow from `roller-compactifications-of-cube-complexes-are-sfts` (PASS, f2a29310d1).
- **Instance (B), surfaces.**
  - (W3) follows from steps (ii)–(iii) of the surface node. Step (i) is replaced by the hypothesis: a wall crossing the common
    perpendicular `σ` and missing both lines separates them.
  - None of these steps uses orientation.
  - (W4) holds because separating walls cross the compact `σ`, and distinct walls are non-asymptotic. Correct.
- **Precisions** (no gap):
  - The Setting should require `𝒲` to be `Γ`-invariant. It is used implicitly for the SFT and the FW corollary, and it holds in both
    instances.
  - In Step 3, "nested" uses that non-crossing walls have one empty quadrant, so that `V_(i+1)^+ ⊆` the far side of `U`. That holds
    in both instances.
- **Corollaries.**
  - `Γ*Z` and minimality rest on `tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts`, which I did not review.
  - "Special groups lie in a finitely presented member of `𝒞`" needs Haglund–Wise for compact special cube complexes (recalled).
  - The FW exclusion is correct: `d` is the wall metric, so an FW subgroup has bounded orbits, and a free action on a locally finite
    graph then forces it to be finite.
