---
rg: 2
id: rational-projective-full-groups-are-finitely-presented
kind: claim
title: The full group of integral projective germs on the rational Cantorization of the m-sphere is finitely presented
distinct_from:
  closed-mcg-embeds-in-rational-projective-full-group: that constructs the host and proves it is full and clopen transitive with the mapping class group inside; this is the remaining finiteness statement about the host.
  train-track-trace-groupoid-hosts-closed-mcg: that phrases finite presentation (its gate G4) for a train-track trace groupoid; this is the same gate for the canonical rational Cantorization host, where gates G1–G3 are already settled.
---

**OPEN** (lane bh-free-54, 2026-09-18).

## Statement

For every `m ≥ 2` (at least for `m = 6g − 7`, `g ≥ 3`), the group
`𝒯_m = [[GL_{m+1}(Z) ⋉ Ŝ_m]]` of `closed-mcg-embeds-in-rational-projective-full-group`
is finitely presented.

## Why it matters

- With `closed-mcg-embeds-in-rational-projective-full-group`, it gives
  Boone–Higman for every closed-surface mapping class group of genus `g ≥ 3`
  (BBMZ Problem 5.3(2)), through `closed-mcg-bh-via-rational-projective-full-group`
  and `fp-clopen-transitive-full-cantor-groups-have-type-a-actions`.
- It would also give an explicit finitely presented full clopen-transitive
  Cantor group containing `SL_{m+1}(Z)`, which is relevant to the open Kazhdan
  questions about Thompson-like groups.

## What is known

- **`m = 1`: settled.** `𝒯_1 ≅ V_{2,4}(⟨σ⟩)`, the Röver–Nekrashevych group of the
  letter flip, which is finitely presented (`rank-one-rational-projective-full-group-is-flip-v`).
- **Hypotheses of the standard simplicity and finite-generation theorems** (not
  applied or read at source here):
  - Hausdorff, effective, minimal, purely infinite, with compact open generating
    set: all proved in the proof route.
  - Expansive: `GL_{m+1}(Z)` is transitive on primitive integral forms, so the
    orbit of the single clopen `H_{x_0}` generates `B_m`.
  - Hence, by Matui's and Nekrashevych's theorems, `[[𝒢]]'` should be simple and
    the alternating full group finitely generated.

## Attempts

1. **Brown's criterion, set up** (lane bh-free-54, 2026-09-18; reasoning only).
   - **The poset.** Take unimodular clopen partitions of `Ŝ_m`, labelled by
     elements of `GL_{m+1}(Z)` identifying each piece with `Δ`, and order them by
     refinement.
   - **Vertex stabilizers.** They are finite: symmetric groups on the pieces,
     times the finite stabilizer of `Δ` in `GL_{m+1}(Z)`.
   - **Directedness.** Any two unimodular fans have a common unimodular
     refinement (common refinement, then toric resolution). So the poset is
     directed and its realization is contractible.
   - **Where it differs from `V`.** In `V`, a leaf splits in exactly one way. Here
     a unimodular simplex has many elementary subdivisions, and not every
     unimodular refinement is reached through finitely many *types* of
     elementary moves. The natural finite-type choice is edge-stellar
     subdivisions at `w_i + w_j`.
   - **What the combinatorics turn on.** Two questions:
     - whether the edge-stellar refinement poset is still directed;
     - whether its descending links are highly connected.

     The first is a strong-factorization question for toric birational maps (an
     Oda-type conjecture, open in dimension ≥ 3 for cones). The weak
     factorization theorem (Włodarczyk; Abramovich–Karu–Matsuki–Włodarczyk) gives
     connectivity by stellar moves and their inverses, which is exactly what is
     needed for the one-dimensional part of such arguments.
   - **Status.** Recorded as the precise combinatorial core of the gate. Nothing
     proved.
2. **Calibration at `m = 1`; the structural break at `m ≥ 2`; a correction**
   (lane bh-free-54, 2026-09-18).
   - **`m = 1` holds.** `rank-one-rational-projective-full-group-is-flip-v`
     proves `𝒯_1 ≅ V_{2,4}(⟨σ⟩)`, which is finitely presented by Nekrashevych's
     theorem for contracting self-similar groups (recalled, not re-read). The
     mechanism is that `SL_2(Z) ∩ Mat_2(Z_{≥0})` is the free monoid on `L, R`, so
     the unimodular subcones form a tree and every germ is a prefix replacement,
     possibly composed with the flip.
   - **`m ≥ 2` breaks the tree.** `C_1 = cone(e_0+e_1, e_1, e_2)` and
     `C_2 = cone(e_0, e_1, e_1+e_2)` are unimodular subcones of `Δ` whose
     intersection has four extreme rays (`e_1`, `e_0+e_1`, `e_1+e_2`, `e_0+e_1+e_2`).
     So:
     - the monoid of nonnegative unimodular matrices is not right-LCM;
     - no subdivision rule makes the unimodular subcones a tree;
     - Nekrashevych's `V_d(G)` framework and X. Li's Garside-category finiteness
       theorem (arXiv:2110.04505) do not apply as stated.
   - **Correction to Attempt 1.**
     - Vertices of the poset are clopen **dissections**, which may have
       T-junctions, not fans.
     - Directedness is then easier than stated: intersect the pieces, triangulate
       each rational polyhedral cone, and resolve each simplicial cone
       unimodularly, one piece at a time. No compatibility across faces is
       needed.
     - The Oda-type strong-factorization remark applies only to a fan-based
       version of the complex.
   - **The decisive test at `m = 2`.** Call a set of at least two pieces of a
     dissection *mergeable* if its union is a single unimodular cone.
     - At `m = 1` every dissection with at least two pieces has a mergeable
       sibling pair, which is the tree property.
     - The question is whether, for `m = 2`, there are dissections of `Δ ⊂ R^3`
       with arbitrarily many pieces and no mergeable set.
     - If yes, the height function "number of pieces" has local minima at
       arbitrary height. Brown's criterion then needs a different Morse function
       or a restricted subcomplex.
     - If no, and the descending links, which are complexes of disjoint
       mergeable sets, are simply connected for large height, then `𝒯_2` is
       finitely presented.
   - **Candidate restricted subcomplex.** Allow only the finitely many types of
     elementary moves up to `GL_{m+1}(Z)`: the stellar subdivision of a piece at
     the sum of the generators of one of its faces. For complete smooth fans,
     connectivity under such moves and their inverses is the weak factorization
     theorem of Morelli and Włodarczyk (recalled, not read at source). Extending
     that to dissections is unchecked.
   - **Status.** Nothing is proved beyond `m = 1` and the non-LCM obstruction to
     the tree route.
3. **Operad reduction; correction to Attempt 2's test; the m = 2 answer so far**
   (lane bh-free-54, 2026-09-18).
   - **Correction.**
     - As stated, Attempt 2's "decisive test" is trivially negative: the set of all
       pieces is always mergeable, with union `Δ`.
     - The meaningful question asks for a mergeable **proper** set: at least 2 but
       not all pieces. A dissection with no such set is *prime*. The primes are
       exactly the minimal nontrivial dissections.
     - In the labelled-partition poset, merging is not geometric. Any `k` pieces
       merge along any `k`-piece dissection of `Δ`, as any two leaves merge in `V`.
       So the geometry enters only through the operad of dissections.
   - **Reduction.** Thumann's `F_∞` theorem for operad groups (arXiv:1409.1085,
     Theorem `41762`, statement read in the LaTeX source) applies to the operad
     `𝒪_m` of labelled unimodular dissections.
     - Every hypothesis except finite type is checked in
       `rational-projective-full-groups-fp-via-thumann-operad-finiteness`.
     - Finite type is the new OPEN premise
       `unimodular-dissection-operad-has-finite-type`.
     - Weak and strong factorization are not needed on this route.
   - **Cocompactness is automatic.** `unimodular-dissections-have-egyptian-fraction-volumes`
     shows that the weights `1/∏h(v)` of the pieces sum to 1. So each piece count
     has finitely many dissections, in every dimension.
   - **The m = 2 answer so far.** The operad is not generated by stellar moves: the
     medial split `M` is a 6-piece prime.
     - A bounded MSI search found primes of sizes 2, 3, 6 and 9–15, with at least 34
       of size 12.
     - It found none at sizes 4, 5, 7 and 8. For sizes up to 9 on fans, and up to 7
       with T-junctions, it enumerated every configuration reachable by local moves.
     - So `𝒪_2` is very likely **not finitely generated**. Thumann's theorem then
       applies only to a finite-type suboperad that the group preserves, and that is
       the Serret gate in operad form.
   - **The arXiv ids given by the coordinator were checked.**
     - `math/9904076` is Włodarczyk, *Toroidal varieties and the weak factorization
       theorem* (general weak factorization, not the toric paper).
     - `alg-geom/9502016` is Lauritzen, on homogeneous spaces in prime
       characteristic, which is unrelated.
     - Morelli's toric paper (J. Algebraic Geom. 5, 1996) was not found on arXiv by
       author search.
     - Also relevant, abstract only: Adiprasito–Pak, arXiv:2404.05930, prove the
       weighted Oda strong factorization conjecture.
   - **Lesson for general BH.**
     - The host-and-embedding half of the Cantor-host route is automatic for any
       group with a faithful piecewise-integral-projective action. The finiteness
       half is a property of one local operad, the same for every such group.
     - The canonical operad fails finite generation in dimension ≥ 2. So the real
       gate is a finite-type coding that the group preserves: the Serret and
       finite-presentation gates are the same gate.
     - The next test is `SL_3(Z) ≤ 𝒯_2` alone: find a finite-type suboperad of `𝒪_2`
       whose operad group contains it.
4. **Cofinality proved; descent not inherited; synchronization isolated** (lane
   bh-free-61, 2026-09-18).
   - **Cofinality.** `edge-splits-cut-every-rational-hyperplane`: a Euclid-type
     potential shows that iterated edge splits cut out every rational hyperplane.
     So the edge-split suboperad is cofinal in `𝒪_m`, and edge-split cells form a
     basis of `Ŝ_m`.
   - **Not factor-closed.** `edge-split-descendants-are-not-factor-closed`: for
     `m = 2`, `cone([[3,2,2],[0,1,2],[1,1,1]])` descends from `Δ` and lies in the
     child `{x_1 ≤ x_0}` without descending from it. Any two children of `Δ`
     still meet in at most two common descendants.
   - **The Serret gate for the edge-split suboperad.**
     `unimodular-cells-synchronize-under-edge-splits` states it as `(Sync_m)`.
     - It is equivalent to directedness of dissections ordered by descent.
     - It follows from a finite matrix game: left row reductions against right
       edge splits.
     - A won game for every unimodular `X` would place all of `𝒯_m` in the
       operad group of the finitely generated edge-split suboperad. That is the
       finite-type suboperad Attempt 3 asks for.
     - Proposed route: a split-lemma induction on the least reachable entry sum.
