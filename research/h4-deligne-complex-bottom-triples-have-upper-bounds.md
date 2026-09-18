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
- **Status.** Open. The computation is evidence and a necessary check, not a proof. A proof needs
  an `H_4` analogue of the auxiliary arrangements of arXiv:2405.12068 §6. The label-5 obstruction to
  the flat-triangle convexity argument (Hoda–Huang arXiv:2602.17983, proof of Thm 5.17, labels ≥ 6)
  is the link-girth angle bound `π(1/2 + 1/3 + 1/m) ≤ π` ⇔ `m ≥ 6`.
