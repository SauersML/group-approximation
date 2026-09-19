---
rg: 2
id: h4-deligne-complex-bottom-triples-have-upper-bounds
kind: claim
title: In the H_4 Deligne complex ordered toward the 5-edge, three pairwise upper-bounded bottom-type vertices have a common upper bound
distinct_from:
  h4-deligne-complex-upward-flag-toward-5-edge: that is upward flagness of the whole H_4 poset; this is its bottom-type case, which implies it given the H_3 theorem.
---

Let `Λ = s_1 s_2 s_3 s_4` be of type `H_4` with `m_{s_3 s_4} = 5`, types ordered
`ŝ_1 < ŝ_2 < ŝ_3 < ŝ_4`. Let `x_1, x_2, x_3` be vertices of `Δ_Λ` of type `ŝ_1`, i.e. left cosets of
the parabolic subgroup `A_{s_2 s_3 s_4}` of type `H_3`, such that for each pair `x_i, x_j` some
vertex of higher type is adjacent to both. Then some vertex is adjacent to all three and has
higher type than `ŝ_1`.

With `h3-deligne-complex-upward-flag-toward-5-edge` and
`spherical-path-upward-flagness-reduces-to-bottom-triples`, this gives
`h4-deligne-complex-upward-flag-toward-5-edge` (route
`h4-deligne-complex-upward-flag-from-bottom-triples`).

## Attempts

- **Configuration.** Take the joins `y_{ij}` (they exist by bowtie freeness). The configuration
  is a 6-cycle `x_1 y_{12} x_2 y_{23} x_3 y_{31}` whose `y`-vertices have types among `ŝ_2`
  (cosets of `A_{s_1} × A_{s_3 s_4}`), `ŝ_3` (`A_{s_1 s_2} × A_{s_4}`) and `ŝ_4` (`A_{s_1 s_2 s_3}` of
  type `A_3`). The claim asks for a filling by three 4-cycles through one vertex. By the
  cycle-to-word translation of arXiv:2405.12068 (Definition `def:ncycle`), this is a statement
  about the products `w_1 ⋯ w_6 = 1` with `w_i` alternating between `A_{s_2 s_3 s_4}` and the
  parabolic subgroups of the `y`-types.
- **How H_3 was done.** The analogous statement for `H_3` is Lemma `lem:triple` of
  arXiv:2405.12068. It projects the 6-cycle to the Coxeter complex, cases on the image (a single
  edge, or two edges), and uses auxiliary sub-arrangements of the `H_3` arrangement whose
  complements carry CAT(0) complexes of groups, then combinatorial Gauss–Bonnet. An `H_4`
  version needs sub-arrangements of the 60-hyperplane `H_4` arrangement with the same
  properties. Not attempted.
- **Finite core check** (w4-042, `experiments/h4-artin-complex-6cycles-2026-09-17/coxcheck.py`).
  The Coxeter complex `C_W` is the positive apartment `{lift(w)A_T}` of `Δ_Λ`. The projection
  `π : Δ_Λ → C_W` (quotient by the pure Artin group) is a type-preserving simplicial retraction
  onto it. So the bottom-triple condition in `C_W` is necessary, and it decides every configuration
  lying in one apartment `g·C_W`. Exhaustive result for `H_4`: 120 `ŝ_1` vertices, 600 `ŝ_4`
  vertices, 1200 pairwise-bounded triples, **0** without a common upper bound. So no counterexample
  lies in a single apartment. The check tells orientations apart:
  - It passes for `B_3`, `H_3`, `B_4`, `D_4`, `A_3`, `A_4`.
  - It fails for the reversed orientations `B_3r` (8 of 32), `H_3r` (20 of 140) and `H_4r`
    (22800 of 152400), and for `A_2`.
- **Garside ball search** (w4-042, same directory, `garside.py`, `tsearch.c`, `README.md`).
  - **Model.** Normalize `x_1 = A_X`, `y_1 = A_Y`, `x_2 = aA_X`, `y_2 = abA_Y`, `x_3 = abcA_X`
    with `X = {s_2,s_3,s_4}` and `Y = {s_1,s_2,s_3}`. A third bound is `uA_Y` with `u ∈ A_X`.
  - **Tests.** Each adjacency `g ∈ A_Y A_X` is tested in exact Garside normal form after padding
    by `Δ_Y^{2K}, Δ_X^{2K}`. Positive answers are certificates.
  - **Balls.** Two kinds are searched. The simple-letter balls `R_T(L)` are products of at most `L`
    signed simples modulo `A_Z`. The pure balls are products of at most `L` standard pure
    generators `w s² w^{-1}`; these are the configurations with `π(ω)` a single edge, i.e. Case 1 of
    `lem:triple` in arXiv:2405.12068.
  - **Calibration.** On `B_3` and `H_3` (known true) every pairwise-bounded triple gets a certified
    common upper bound, in both ball types. On `A_3` (not covered by the conjecture) 245 simple-ball
    and 76 pure-ball triples stay unresolved.
  - **H_4 results.** No unresolved triple in any ball searched:
    - `(La,Lb,Lc,Lu) = (1,1,1,1)`: 480 bounded nontrivial triples.
    - `(2,1,2,1)`: 4520, with identical counts at `K = 3, 4, 6`.
    - Pure `(2,1,2)` with `u ∈ R_X(1)`: 7934.
    - `(2,2,2,2)` with `|R_X(2)| = 1810`, run one `a` at a time. Complete, in `H4_22222.out`:
      4300560 words, 168240 bounded nontrivial triples, all found, 0 candidates.
    - Pure `(2,2,2)` with `|PX(2)| = 709`, `u ∈ R_X(1)`. Complete, in `PH4_22212.out`:
      4305048 words, 164002 bounded nontrivial triples, all found, 0 candidates.
  - **What it rules out.** No counterexample is a 6-cycle whose words lie in these balls, among
    those whose adjacencies are certified at the stated padding.
  - **Structural hint.**
    - With `b ∈ R_X(1)`, and in all pure runs, every witness was `y_2` or lay in `R_X(1)A_Y`.
    - With `b ∈ R_X(2)`, witnesses of length 2 are needed (index up to 1802).
    - So the witness length tracks the length of `b`, which is consistent with a quasi-centre built
      from the middle letter.
- **Single-edge case: normal form and fibred quotient** (w5-042,
  `h4-case1-pure-normal-form-and-fibred-obstruction`). Case 1 (hexagon projecting to one edge) is equivalent
  to tuples `α_i ∈ F = ker(ρ_X|P_Y) ≅ F_3` and `β_i ∈ N = ker(ρ_Y|P_X)` with `∏α_i = ∏β_i = 1` and
  `α_1β_1α_2β_2α_3β_3 = 1`.
  - Any sub-arrangement of `𝒜_x ∪ 𝒜_y` is blind to the last relation, because `[N, F] = 1` in its `π_1`. So an
    `H_4` auxiliary arrangement must use other walls.
  - Adding the third wall of an `A_2` flat `w ∩ w'` gives a 19-wall arrangement in which `ℓ_x` is still
    modular. Its `π_1` is `F_4 ⋊ P_X`. In it `[N, F] ≠ 1`, and the relation becomes a nontrivial
    point-pushing identity.
  - Open: turning that identity into a centre (the Gauss–Bonnet step).
- **Single-edge case: braid monodromy of the fibred shadows** (w6-042,
  `h4-a2-fibred-shadows-are-a4-pure-braid-retractions`).
  - Every `ℓ_x`-fibred shadow embeds the hexagon relation in a pure braid group `P_{k+1}`.
  - For each of the 9 `A_2` flats, the monodromy `P_X → P_4` kills 9 of the 15 meridians and sends the other 6
    to the `A_ij`.
  - The shadow is the retraction `P ↠ P_5` onto an `A_4` braid sub-arrangement, with `F ↦ ⟨A25,A35,A45⟩` and
    `N ↦ ⟨A12,A13,A14⟩`.
  - Consequence: the point-pushing identity in one `A_2` shadow is exactly the `A_4` single-edge hexagon
    relation, so it cannot force a label-5 centre. The `A_2` augmentations are dead as `H_4` analogues of
    Huang's arrangement I.
  - What remains among single fibred flats is the three `I_2(5)` flats: 6 fibre points, a `P_7` shadow, and
    collision arrangement `χ = (t−1)(t−4)(t−5)`.
- **Single-edge case: the `I_2(5)` fibred shadows** (w6-042,
  `h4-i25-fibred-shadows-are-rigid-cluster-braid-groups`).
  - Four fibre points form a rigid cluster `p_c + s·{0, 1, φ^{-1}, φ}`, the `I_2(5)` pencil, and they all
    collide on one wall.
  - The shadow is `f^{-1}(⟨Δ²_C⟩) ⊂ P_7`, the subgroup where the cluster moves only by full twists.
  - The identity is an `A_6` single-edge hexagon whose `N`-letters lie in the rigid-cluster subgroup `N_V`.
  - Open: whether every such constrained hexagon has a centre `ρ_V(y_2)` or `ρ_V(s_4^k)A_{Y''}`.
- **Single-edge case: centre forms in the `I_2(5)` shadow** (w7-042,
  `h4-i25-shadow-centre-forms-hold-only-up-to-rotation`).
  - **The literal forms fail.** A cabling embedding `ι : P_4 → P_7` (`F → F''`, `N → N_V`, `A_{12} ↦ Δ_C^2`)
    carries an exact `A_3` tuple to a hexagon of the constrained class. Certified in curver, that hexagon has:
    - `y_2 ≁ x_1`;
    - no centre `Δ_C^{2j}A_{Y''}` for any `j`, by the twist inequality;
    - but its own vertex `y_3` as a centre.
  - **Rotated, the forms hold.** "`y_3` is a centre" is form (Y2) after re-basing at `(x_2, y_1)`. On every tested
    tuple, some rotation has form (Y2) or (TW):
    - 224 exact `A_3` tuples;
    - 180 exact `A_6` tuples;
    - all 32 closing `A_3` hexagons that fail the base-edge forms, each of which has `y_3` as a centre.
  - **The single flat is exhausted.** An `A_3` pair lemma (1910 tests, 0 violations, unproved) would give every
    `ι`-cabled hexagon a centre. So a single `I_2(5)` flat cannot produce a counterexample, and a proof of
    Case 1 must use its rotation-invariant form with multi-flat or non-fibred shadows.
- **Single-edge case: the pair lemma, and all braid shadows have centres** (w8-042,
  `braid-pure-single-edge-hexagons-always-have-a-centre`,
  `h4-fibred-braid-shadows-cannot-certify-case1-counterexamples`).
  - **`Z/2` Helly lemma (proved).** Let `x_i` be arcs from punctures to a boundary point `d_0` of a punctured
    disc. The set of punctures in the `d_1`-region of `⋃x_i` is the intersection of the sets for the pairs
    `x_i ∪ x_j`.
    - Proof: the face boundary of a separated puncture is a mod-2 cycle. It splits into tails `π_i(v)` running to
      `d_0`, and these pair up into cycles on `x_i ∪ x_j`.
    - Consequence: every pure single-edge hexagon in the `(A_X, A_Y)` arc model of `B_n` has a spider centre.
      The `A_Y` are spider stabilisers, and all ranks are covered.
    - This proves w7-042's `A_3` pair lemma. Cross-check: 0 violations in 1910 / 3663 / 4223 triples at
      `n = 4, 5, 6`.
  - **Obstruction.** The `A_2` and `I_2(5)` fibred shadows, and products of them such as `N_V ∩ N_{V'}`, send
    Case 1 hexagons to pure braid hexagons, so every image has a centre.
    - No fibred braid shadow can certify a centreless Case 1 hexagon. This kills the cabling route
      unconditionally, and the whole class `𝓗_V` as a source of certificates.
    - For the `A_2` flats (onto `P_5`), some image centre even lies in the image layer.
    - What is left is lifting. In an `I_2(5)` shadow: is some centre in `Ω(x_1∪x_2∪x_3)` a spider whose
      restriction to the cluster `C` is `Δ_C^{2j}y_0`, and does it lift to an `H_4`-adjacent vertex? That is
      form (R).
- **Single-edge case: (L_V) is dead, image-layer centres always exist** (w9-042,
  `h4-i25-shadow-hexagons-have-image-layer-centres`).
  - **Ejection-arc lemma (proved).** Every `I_2(5)` shadow hexagon `ρ_V(H)` has a centre `hA_{Y''}` with
    `h ∈ G_V`. Equivalently, `⋂_i ρ_V(p_iP_XP_Y) ≠ ∅`.
    - If the cluster point `p_c` lies in the `d_1`-region `Ω`, every twist class `D^j` is realised.
    - Otherwise the arc ejecting `p_c` to `d_0` is unique in the forgotten 4-point disc. It is shared by every
      pair region that ejects `p_c`, and in `B_4` a 3-leg spider has exactly one disjoint such arc. This pins
      the class of *every* centre to `f(h) ∈ D^m P_{123}`, with one `m` common to those pairs.
  - So the last single-flat certificate, (L_V), never holds. The lifting step (b) is equivalent to Case 1:
    `ρ_V(⋂p_iP_XP_Y) ⊆ ⋂ρ_V(p_iP_XP_Y)`, and the gap is `ker ρ_V`.
  - **Two flats are not fibred.** For every pair of the three `I_2(5)` flats, `ℓ_x` is not modular in
    `ℬ_V ∪ ℬ_{V'}` (23 walls, 8 fibre points). The new cluster points of the two flats collide on 2 hyperplanes
    that are not `H_4` walls (`twoflat.py`). So there is no braid picture with two rigid clusters. A multi-flat
    joint certificate has to be computed in the non-fibre-type group `π_1M(ℬ_V ∪ ℬ_{V'})`, or in a
    non-fibred shadow.
- **Two-flat joint centres reduce to one pencil loop** (w10-042,
  `h4-i25-two-flat-joint-centres-reduce-to-pencil-loops`, established).
  - *Centre criterion.* In a fibred shadow `F_k ⋊ B`, `c ∈ B` is a centre iff `α_1` and `β_1α_2β_1^{-1}`
    lie in `cF_Yc^{-1}`.
  - *Reduction.* A joint centre `g ∈ P_XP_Y` for `(V_a,V_b)` exists iff the two single-flat solution sets
    meet in `B_{ab} = π_1M(base_a ∩ base_b) = P_4 ×_{P_3} Π_{ab}`. Here `Π_{ab} = π_1(ℂ² ∖ 5` concurrent
    lines`) ≅ ℤ × F_4`.
  - *What is new.* `P_4` is the `A_4` core, which is already an `A_2` shadow. So the only new condition is
    that the loop of `p_{b+1}` around the rigid cluster `C_a` matches the loop of `p_{a+1}` around `C_b`.
    Both lie in the same 5-line pencil: `x2, x3` for `(V_0,V_1)`.
  - *Correction to w9.* Fibred two-cluster shadows do exist: 6 of them, each with two 3-point clusters and
    a double collision wall.
  - *Machine check.* In all 180 length-1 tuples, `p_c` is never ejected, so no class is
    pinned and the tuples give no candidate.
  - *Next.* Search for tuples in which both flats eject their cluster point, and compare their
    `Π_{ab}`-classes.
- **Joint shadow certificates see only vertex-free tuples** (w11-042,
  `h4-i25-joint-certificates-refute-only-vertex-free-tuples`, established plus machine).
  - *Vertex criterion.* With `c_01 = β_1α_2β_1^{-1}`, `c_12 = β_1^{-1}α_1β_1` and `c_20 = β_3α_1β_3^{-1}`, the
    hexagon vertex `u_P` is a pure centre iff `c_P ∈ F·P_X` (for `P = 12`, iff `c_12 ∈ P_X·F`).
  - *Shadow form.* In each fibred shadow, `ρ_a(b_P) ∈ Sol_a` iff `ρ_a(c_P) ∈ F^{(a)}_Y`.
  - *Consequence.* Every multi-flat joint certificate, including w10's `Π_{ab}` pencil-loop matching, can
    refute only tuples in which each `P` fails in some shadow.
  - *Machine.* Double ejection is common. Exact Garside tuples with `|α| ≤ 1, |β| ≤ 2` and `|α| ≤ 2, |β| ≤ 1`
    give 1224 and 1368 doubly ejected tuples, and zero-winding commutator searches give 368 more.
  - *No mismatch.* Every doubly ejected tuple has a common ejecting pair. A Burau-hashed search, complete for
    its word lengths (`|α| ≤ 2, |β| ≤ 2` and `|α| ≤ 3, |β| ≤ 1`: 91360 and 53156 genuine tuples, plus 14832 from a partial `|α| ≤ 1, |β| ≤ 3` run), finds 0 vertex-free tuples: every genuine tuple has a Garside-verified `c_P ∈ F`. So no
    `Π_{ab}` mismatch occurs.
  - *Next.* Prove (VC), that every Case 1 tuple has a pure centre among `u_01, u_12, u_20`; this would settle
    Case 1. Otherwise, find a vertex-free tuple at longer words and only then run the joint test on it.
- **Pure bounds of Case 1 are a conjugate-membership problem** (w12-042,
  `h4-case1-pure-centre-iff-px-conjugate-of-f-holds-triple`, proved; searches are evidence).
  - **Reformulation.** Put `e_0 = α_1`, `e_1 = β_1α_2β_1^{-1}` and `e_2 = (e_0e_1)^{-1}`. The homomorphism `ρ_X`
    shows that a Case 1 hexagon has a pure `ŝ_4` bound iff `⟨e_0, e_1⟩ ≤ γFγ^{-1}` for some `γ ∈ P_X`.
  - **Vertex criterion.** A hexagon vertex is such a bound iff `γ ∈ {1, β_1, β_3^{-1}}` works. So the vertex
    criterion (V) is exactly `c_P ∈ F`, and it is decided by the Garside test `fmem.py`.
  - **No free-product shortcut.** `F ∩ s_4^2Fs_4^{-2} ⊇ ⟨p_2, p_3⟩` while `s_4^2Fs_4^{-2} ≠ F`.
  - **Searches.** Transporter triangles, pair twists and the `|α| ≤ 1`, `|β| ≤ 3` vertex search (34 of 36 letter pairs) found no
    vertex-free tuple.
  - **Next.** Find an action of `ker ρ_X` on a tree (or a CAT(0) complex) whose vertex stabilisers are the
    `γFγ^{-1}`. Serre's lemma then gives Case 1 in full.
- **Case 1 Helly is a commutator double-coset problem** (w13-042,
  `h4-case1-helly-is-a-commutator-double-coset-problem`; proved, searches are evidence).
  - **Rigidity.** Applying `ρ_Y` shows that conjugation by `γ ∈ N` fixes every element of `P_Y` that it keeps in
    `P_Y`. Hence `F ∩ γFγ^{-1} = C_F(γ)`.
  - **Exact pure bounds.** The pure bounds of a Case 1 tuple are exactly the `γA_Y` with
    `γ ∈ C_N(α_1) ∩ β_1C_N(α_2)`. So (H) holds iff `β_1 ∈ C_N(α_1)C_N(α_2)`.
  - **Commutator form.** With `a = α_1^{-1}`, `b = α_2`, `u = β_3` and `v = β_3β_1`:
    - `(*)` says `[u, a] = [v, b] =: k`;
    - the pure bounds are the `w ∈ N` with `[w, a] = [w, b] = k`;
    - the three hexagon vertices are `w = 1, u, v`.
  - **Diagonal pairs.** For `α_1 = α_2`, (H) and VC are equivalent. This closes the two diagonal pairs that `vsearch3`
    could not finish.
  - **Search.** An exact hash-class search over `N`-elements of length ≤ 3 (12 letters) and all `F`-pairs of length
    ≤ 2 found no VC-failure.
  - **Next.** Case 1 is now equivalent to `(H″)`: for `a ≠ b` in `F` and `u, v ∈ N`, `[u, a] = [v, b]` implies
    `u^{-1}v ∈ C_N(a)C_N(b)`. It needs an invariant of `⟨N, F⟩` finer than `(ρ_X, ρ_Y)`, e.g. a tree for `⟨N, F⟩` whose
    edge groups at `F` are the `C_F(n)`.
- **Commutator Helly holds in type A, but vertex centres fail there** (w14-042,
  `h4-case1-commutator-helly-holds-in-type-a-but-vc-fails`; (Q) and (A) proved, (B) certified, searches are evidence).
  - **Cosets.** `U_a(k) = {u ∈ N : [u, a] = k}` is empty or a coset `uC_N(a)`. So (H″) for `(a, b, k)` says the
    cosets `U_a(k)` and `U_b(k)` meet. When they meet with `k ≠ 1`, VC fails iff `C_N(a)` and `C_N(b)` are
    incomparable.
  - **Type A.** In every `A_n`, (H″) holds. The reductions of w12 and w13 use only facts true for `B_{n+1}`, and the
    arc-model Helly theorem (`braid-pure-single-edge-hexagons-always-have-a-centre`) supplies the pure centre.
  - **VC is false in A_4.** In `B_5`, take `a = p_1p_0`, `b = p_2p_0`, `u = x_2x_0` and `v = x_2x_0x_1x_0^{-1}`.
    - This is a Case 1 tuple with no vertex centre; its pure centre is `x_0^{-1}A_Y`.
    - It is certified in the faithful Artin representation.
    - An exact Garside search counts 18720 VC failures at radii (3, 6).
  - **H_4 search.** An exact hash search at F-radius 3 and N-radius 4 found no VC failure and no Helly candidate. It
    covered 187 `F`-elements, 305265 `N`-elements and 954436 tuples.
    In the reversed H_4 orientation, which the target does not cover, VC already fails at radii (2, 4) (2688 tuples), but
    every failure has a centre inside the ball.
  - **Next.** A uniform proof of Case 1 cannot always give a hexagon vertex. It needs an H_4 analogue of the Z/2 Helly
    argument that reaches non-vertex centres, or a proof that the H_4 centralisers `C_N(a)` are nested whenever the
    cosets meet. A ball search cannot refute (H″); only a finite-quotient obstruction can.
  - **Lifting test.** Vertex centres map to vertex centres under the fibred braid shadows. So an H_4 Case 1 hexagon
    whose `P_5`-shadow is the A_4 example would refute VC in H_4. Finding one is the lifting problem.
- **Status.** Open. The computation is evidence and a necessary check, not a proof. A proof needs
  an `H_4` analogue of the auxiliary arrangements of arXiv:2405.12068 §6. The label-5 obstruction to
  the flat-triangle convexity argument (Hoda–Huang arXiv:2602.17983, proof of Thm 5.17, labels ≥ 6)
  is the link-girth angle bound `π(1/2 + 1/3 + 1/m) ≤ π` ⇔ `m ≥ 6`.
