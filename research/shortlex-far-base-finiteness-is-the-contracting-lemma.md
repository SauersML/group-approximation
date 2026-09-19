---
rg: 2
id: shortlex-far-base-finiteness-is-the-contracting-lemma
kind: claim
title: For an ordered generating set of a hyperbolic group whose ShortLex descent trees at adjacent bases refine each other with bounded delay (not automatic), induction along a geodesic makes the group a rational similarity group on the ShortLex boundary with offsets bounded linearly in word length; far-base finiteness is exactly a uniform offset bound, i.e. the contracting property, so on this route the F_infinity question is BBMZ Question 1.2 again, for hyperbolic buildings as well
requires:
  - shortlex-cone-tiles-certify-upstream-leaving-crossing
distinct_from:
  shortlex-cone-tiles-certify-upstream-leaving-crossing: that proves exact finite-type cone tiles and, by one computation, one-level mutual refinement at adjacent bases; this runs the induction to far bases, derives rationality and the RSG property, and identifies far-base finiteness with contraction.
  hyperbolic-groups-quasi-isometrically-embed-in-fp-simple-groups: that is Zaremsky's open F_infinity question; this shows the tile-and-operad route to it reduces to BBMZ Question 1.2 in the ShortLex coding too, and does not bypass it.
---

**Status.**
- **ESTABLISHED (lane proof, bh-finf-hyp, 2026-09-19; elementary; Referee bh-ref-q11 2026-09-19: PASS for Lemmas 1–2 and Theorem 3.1–3.3, conditional on (M1); item 4 needs Busemann normalization, see the Referee section):** Lemmas 1–2 and Theorem 3,
  under hypothesis (M1).
- **Scope (restated 09-19).** Everything here holds for an ordered generating set `(S,<)` satisfying (M1), or
  more generally (M1_D) below.
  - Neither is a consequence of hyperbolicity: (M1_D) fails for every `D` for a virtually free right-angled
    Coxeter group with a suitable order (`shortlex-adjacent-refinement-fails-for-a-virtually-free-racg`).
  - (M1) was checked computationally at depths ≤ 4–6 on F2, the right-angled pentagon group and the (4,4,4)
    Coxeter group (`research/artifacts/gq-bh-finf-hyp-shortlex-crossing-test.md`).
- **Reduction (item 4):** proved given its inputs, in the Busemann-normalized form required by the referee.
- **Buildings:** not verified (see the referee section).
- No priority is claimed, and no new computation was run.

## Setting

- The notation is that of `shortlex-cone-tiles-certify-upstream-leaving-crossing`. `𝒯_x` is the descent tree at
  base `x`. Its node `z` has depth `d(x,z)` and tile `T_x(z) = z·C(x^{-1}z)`, taken on `∂Ω`.
- For buildings, with chambers as nodes and `W`-valued ShortLex types, the same statements are expected but not
  verified (see the referee section).
- **(M1).** For every `s ∈ S`, the depth-`n` tiles of each of `𝒯_1`, `𝒯_s` are unions of depth-`(n+1)` tiles of
  the other.
- **(M1_D)** (bounded left delay `D`): the same with `n + D` in place of `n + 1`. Under (M1_D), Lemma 2 holds with a
  loss of `D` per step, and item 3 holds with `|w| = n − D|g|` and `|h| ≤ (D+1)|g| + 4δ`.

## Lemma 1 (sandwich)

Suppose each block of a partition `𝒫` is a union of blocks of a partition `𝒬`. Then each `𝒬`-block lies in
exactly one `𝒫`-block. So under (M1), every depth-`(n+1)` tile of one tree lies inside a single depth-`n` tile of
the other. ∎

## Lemma 2 (induction along a geodesic)

Let `1 = g_0, g_1, …, g_m = g` be a geodesic. Every depth-`n` tile of `𝒯_g`, for `n ≥ m`:
- lies inside a single depth-`(n − m)` tile of `𝒯_1`;
- is a union of depth-`(n + m)` tiles of `𝒯_1`.

*Proof.* Translating (M1) by `g_{i−1}` gives it for the pair `𝒯_{g_{i−1}}, 𝒯_{g_i}`. Chain the containments of
Lemma 1 `m` times, losing one level per step. The unions refine one level per step. ∎

## Theorem 3 (rational RSG on the ShortLex boundary, assuming (M1))

Let `Γ` be hyperbolic and prune the cone types with finite cones.

1. **The boundary is the cone-type SFT.**
   - The `𝒯_1`-tiles form a basis of `∂Ω`.
   - `∂Ω` is the space of infinite paths from the root in the cone-type automaton, i.e. a cone in an SFT `Σ`.
2. **Canonical similarities come from `Γ`.** If `C(y) = C(y')`, then `y'y^{-1}` maps `T_1(y)` onto `T_1(y')` and
   is the identity in addresses. So the image of `Γ` is an RSG in the sense of BBMZ `def:rsg`.
3. **Every element is rational, with linear offsets.**
   - For `g ∈ Γ` and a node `y` of depth `n > |g|`, `g·T_1(y) ⊆ T_1(w)` for a node `w` of depth `n − |g|`.
   - The local action of `g` at `y` is `v ↦ hv` in ShortLex coordinates, with `h = w^{-1}gy`. It is determined by
     `(h, C(y), C(w))`, and `|h| ≤ 2|g| + 4δ`.
   - So each `g` has finitely many local actions, and `Γ ≤ R_Σ`.
4. **Far-base finiteness equals contraction (Busemann-normalized, corrected 09-19).** Suppose there is `c` such
   that for all `g` and all deep enough `y`, `g·T_1(y)` lies in a single `𝒯_1`-tile whose node `w` has depth
   `≥ |gy| − c`. Equivalently the depth is `≥ n + β − c` with `β = |gy| − |y|`.
   - Then `|h| ≤ c + C_δ` uniformly, with `C_δ` depending only on `δ`. The nucleus lies in the finite set of
     triples `(h, κ, κ')` together with a bounded prefix, and `Γ` is a **contracting RSG**. Its full closure is a
     full contracting RSG.
   - Conversely (sketch), a uniform bound on `|h|` for deep nodes bounds this normalized loss.
   - The earlier form, "depth `n − c`", is never satisfied by a non-elementary `Γ` (referee), and it is withdrawn.

## Proofs

**1.**
- The cylinders "`a(x) = t`" generating the topology of `Ω` are depth-1 tiles of `𝒯_x`.
- By Lemma 2 each is a finite union of `𝒯_1`-tiles. So the `𝒯_1`-tiles generate the topology.
- Nested `𝒯_1`-tiles along a path are nonempty (after pruning) and compact, so each path determines exactly
  one point.
- The path language is the ShortLex language, which is regular. Its automaton, with the finite cone types
  pruned, is an SFT presentation.

**2.**
- `y'y^{-1}·yC(y) = y'C(y')`.
- A point with address `SL(v)` below `y` goes to the point with address `SL(v)` below `y'`.

**3.**
- **Containment.** `g·T_1(y) = T_g(gy)` is a depth-`n` tile of `𝒯_g`. Apply Lemma 2.
- **Local action.** In coordinates of `T_1(w) = wC(w)`, the point `y v` goes to `g y v = w·(hv)`, whose address
  below `w` is `SL(hv)`. So the map depends only on `h`, the source cone `C(y)`, and the target cone `C(w)`.
- **The offset bound.** Take a far point `x ∈ g·T_1(y)`.
  - `w` lies on the ShortLex geodesic `[1,x]`, and `gy` on the geodesic `[g,x]`.
  - `d(w,x) − d(gy,x) = (|x| − n + |g|) − (d(g,x) − n) ∈ [0, 2|g|]`, since `||x| − d(g,x)| ≤ |g|`.
  - Two geodesics to `x` from points at distance `|g|` are `2δ`-close at equal distance from `x`, far from their
    start.
  - So `d(w, gy) ≤ 2|g| + 4δ`.
- **Finiteness.** There are finitely many triples for each `g`, and finitely many nodes of depth `≤ |g|`.

**4.**
- **Nucleus bound.** Take a far point `x ∈ g·T_1(y)`.
  - The 1-geodesic to `x` passes within `2δ+1` of `gy`, near depth `|gy|`. `w` lies on that geodesic at depth in
    `[|gy| − c, |gy| + 2δ + 1]`.
  - So `w` and `gy` are at distances from `x` differing by at most `c + O(δ)`, on two geodesics to `x` that are
    `2δ`-close there. Hence `|h| = d(w, gy) ≤ c + C_δ`.
  - The BBMZ local action is taken at the maximal common prefix, which lies within a further bounded depth, as the
    referee notes. So all local actions at deep nodes lie in a finite set.
- **Nucleus of injections.** BBMZ `prop:NucleusHasProperties` makes this nucleus a nucleus of injections, and
  `thrm:RSGCharacterization` gives the full closure.
- **Converse (sketch).** If `|h| ≤ H` for deep nodes, then `w` lies within `H` of `gy`, so its depth is at least
  `|gy| − H`. That is the normalized hypothesis with `c = H`. ∎

## What this says about the F_∞ question

- **Far-base finiteness is the contracting lemma.** The finite spine of tile trees at far bases, up to the group,
  is exactly the finite nucleus. The adjacent-base computation, carried along geodesics, gives rationality with
  linear offsets (item 3), the ShortLex analogue of Belk–Bleak–Matucci's rationality. It does not give
  contraction. Contraction needs the losses not to accumulate (item 4), which is the ShortLex counterpart of
  BBMZ's contracting lemma `lem:contractinglemma`.
- **If contraction holds, the host is again a full contracting RSG.** It is finitely presented, and simple after
  the usual envelope (BBMZ `thrm:fin_pres`, `prop:contr_to_simple`). Its `F_∞` is BBMZ Question 1.2, verbatim.
  The ShortLex coding gives canonical, branching-free addresses, but the same open question.
- **The Thumann operads do not escape this.**
  - With only the canonical splits, the operad group contains `g` only if deep tiles match exactly, one tile onto
    one tile (`C(gy) = C(y)` eventually). Item 3 gives containment in a tile and unions of tiles, not matching.
  - With union splits, the tile-type non-surjective local actions are the nucleus-tile operad of
    `hyperbolic-cone-matching-holds-off-the-branch-locus`, whose square filling fails at branch rays, as in
    `pentagon-reflection-group-fails-cone-matching-at-wall-ends`.
- **Kazhdan building lattices.** (Not verified; see the referee section. Item 2 needs a chamber-free, chamber-transitive
  action or stabilizer bookkeeping.) Thickness `q` only enlarges the cone-type SFT: for `GQ(q,q)` residues each
  panel adds `q` branches. Lemma 2 and Theorem 3 are unchanged. So the `q ≥ 7` candidate is a (conditionally)
  contracting RSG, and its `F_∞` is Question 1.2 for that RSG. It is not a new finiteness mechanism.

## Lesson for general BH

- **Coding changes cannot bypass the finiteness question for boundary hosts.**
  - Any exact finite-type tile coding on which `Γ` acts by finite-state maps makes `Γ` an RSG.
  - Its far-base finiteness is exactly the contracting property.
  - So `F_∞` of the resulting full group is BBMZ Question 1.2 in every such coding, whether horofunction atoms,
    ShortLex cones or building chambers.
- **What an F_∞ proof for all hyperbolic groups needs.** Either a solution of Question 1.2, i.e. a finiteness
  complex for full contracting RSGs with nontrivial nucleus, or a host that is not a boundary full group. The
  thick-building candidate supplies neither by itself.
- **What remains of the building route.** Its value is as a test case for Question 1.2 with Kazhdan acting group,
  where cube-complex (median) methods are provably unavailable.

## Next

- **Try Question 1.2 directly, in its simplest nontrivial case: a contracting RSG whose nucleus is the ShortLex
  offset triples.** A candidate complex is Belk–Hyde–Matucci's germ complex, with "offset germs" `(h, κ, κ')` in
  place of point germs. Calibrate its descending links on `F_2` with a non-basis generating set, where the ShortLex
  nucleus is nontrivial. Check first whether that full closure is already known to be `F_∞`.
- **Prove (M1) for hyperbolic groups, or find a counterexample.** It is a bounded-delay statement for left
  multiplication on ShortLex words.

## Referee (bh-ref-q11, 2026-09-19): Lemmas 1–2 and Theorem 3.1–3.3 PASS conditional on (M1); item 4 as stated is VACUOUS and needs Busemann normalization; grading below

**Grading.**
- **Lemma 1: unconditional, correct.** It needs tiles of a fixed depth to partition `∂Ω`.
- **Lemma 2: correct given (M1)**, for all depths and all `s`, with the equivariance `g·𝒯_x = 𝒯_(gx)`.
- **(M1) is conditional.** It was checked only at depths `≤ 4–6`, on four examples. It is a bounded-lookahead statement for the base-change map on ShortLex rays. ShortLex automaticity gives fellow-travelling of `SL(x)` and `SL(sx)`, but not by itself a deterministic output with delay 1, so (M1) is a conjecture.
  - A delay-`k` version would be enough for Lemma 2 and items 1–3, with losses of `k` per step.
- **Theorem 3.1–3.3: correct given (M1).** The offset computation `d(w,x) − d(gy,x) = |x| − d(g,x) + |g| ∈ [0,2|g|]` is right, and gives `|h| ≤ 2|g| + 4δ`.
  - **Precision.** BBMZ local actions are taken at the *maximal* common prefix of `g·T_1(y)`, which can be deeper than `w`. It is still at depth `≤ n + |g|`, since `g·T_1(y)` contains a depth-`(n+|g|)` tile. So each `g` still has finitely many local actions, indexed by `(h, C(y), C(w))` plus a prefix of length `≤ 2|g|`.

**Item 4: the depth normalization is wrong.**
- As stated, the hypothesis ("`g·T_1(y)` lies in a single `𝒯_1`-tile of depth `n − c` for all `g` and deep `y`") is never satisfied by a non-elementary `Γ`.
- Take `g = u^{-1}` with `u` a prefix of `y`, `|u| = k > c`. Then `g·T_1(y) = (u^{-1}y)·C(y)` sits at depth `n − k`. Its points share only the prefix `u^{-1}y`, because `C(y)` branches within bounded depth after pruning. So it lies in no depth-`(n−c)` tile.
- The same computation shows the flaw in the proof: with `w` at depth `n − c`, the difference `d(w,x) − d(gy,x) = |x| − d(g,x) + c` ranges over `[c−|g|, c+|g|]`. That does not give `|h| ≤ 2c + 4δ`.
- **Correct form.** Measure the loss against the Busemann shift: "`g·T_1(y)` lies in a single `𝒯_1`-tile of depth `≥ |gy| − c`", equivalently `≥ n + β − c` with `β = |gy| − |y|`. Then `w` and `gy` are at nearly the same depth on nearly the same geodesic, so `|h| ≤ c + O(δ)`. Conversely, `|h| ≤ H` bounds that loss.
- This is the "level = Busemann shift up to bounded error" condition of the surface and greedy-cube proofs.
- With this correction, the reduction to BBMZ Q1.2 ("Do full, contracting RSGs have type F∞?") holds, conditional on (M1) and on the corrected far-base bound, which is itself unproved here.

**Buildings.** Not verified.
- Item 2 needs `y′y^{-1} ∈ Γ` carrying tiles, which requires a chamber-transitive and free action or a stabilizer bookkeeping that the node does not give.
- (M1) was checked only on a `GQ(2,2)` example.
- So "Lemma 2 and Theorem 3 are unchanged" for Kazhdan building lattices is a conjecture.
