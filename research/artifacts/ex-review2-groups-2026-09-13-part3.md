# EX review, wave 2, part 3: the a7a7a8 linear-representation certificates, rerun (2026-09-13)

Lane `ex-verify2-groups`. Index: `ex-review2-groups-2026-09-13.md`. Read at tip `7d41d1a16`.
Sources: `research/artifacts/hyperbolic-triangle-linear-search-2026-09-13.md` and
`experiments/hyperbolic-triangle-search/{lin4,lin5,linD,linZ,cands}.py`. The backlog pass
(`ex-review-backlog-2026-09-13-part6.md` §17) checked the method and the module lists, and did not rerun anything.

## 1. The rerun

- **Where.** MSI (sioux node), `module load sagemath/10.7`, one core, `DOT_SAGE` in the lane's scratch directory,
  `/scratch.global/sauer354/ex/ex-verify2-groups/tri/`. The scripts were taken from main at `7d41d1a16`, with
  checksums matched after upload.
- **Jobs.** `lin4.py cal`, `lin4.py cands`, `lin5.py cal`, `lin5.py cands`, `linD.py d6c2 cands`, `linZ.py cal`,
  `linZ.py 1`, `linD.py d7c0 cands` and `linZ.py 2,3,4`. They took 9 to 72 s of wall time each, and every exit was 0.
- **Comparison.** Each output was diffed against the file of the same name on main, after replacing every
  `<float>s` timing by a placeholder and dropping the `EXIT`/`DONE` lines. All nine are **identical**, with equal
  line counts (19, 34, 18, 34, 6, 4, 4, 6, 8).
- **What the outputs say.**
  - `lin4`/`lin5`: `G_1` and `G_3` have trace ideal `(1)` on both passing type triples. For `G_2` and `G_4` all eight
    type triples fail the characteristic-polynomial test.
  - `linD d6c2` and `linD d7c0`: `(1)` for all four candidates.
  - `linZ`: a strong integral Gröbner basis `{1}`, so `N = 1`, for all four.
- **Calibrations.**
  - `lin4 cal` finds the recorded points on literal `(A_8,A_8,A_8)` and twisted `(A_7,A_7,A_7)` triangles, each
    checked against the relators. So the code does find homomorphisms when they exist.
  - `lin5 cal` gives non-`(1)` ideals.
  - `linZ cal` gives no integer element.
- **Not rerun.** The projective `μ_7`-twists (`linD_d7p29_twist`, `d7p43`) and the stopped integral twisted runs. The
  node records these only as partial, and claims nothing beyond them.

This is a reproduction of the code's outputs, not a line-by-line audit of the code. The positive calibrations are
the check that the pipeline can see homomorphisms.

## 2. The mathematics behind the certificates

- **Vertex-injectivity.** Suppose `φ` is trivial on `A`. Then `x_B = q^(e1)` dies, and `B` is simple and generated
  by `x_B, y_B`, so `B` dies. Then `r` dies, and so does `C`.
- **Torus parametrization.**
  - A 7-element has 4 (resp. 7) distinct eigenvalues on `4` (resp. on `1 ⊕ 6` and the heart `7`), so its centralizer
    is a torus.
  - Every `β` of the fixed type with `β(x_B) = t` is `S H S'^(-1) β_0 (S H S'^(-1))^(-1)`.
  - Scalars act trivially, so one coordinate normalizes.
  - The trace equations are necessary, and `GB = [1]` excludes all points over the algebraic closure.
- **The sign lemma (§3 of the artifact), re-derived.**
  - A 7-element acts on `4` with eigenvalues `{1, ω^a, ω^(2a), ω^(4a)}`, so `τ = χ(a)` is well defined. Dualizing
    sends `a -> -a`, and `χ(-1) = -1`. Also `τ(g^e) = χ(e) τ(g)`.
  - The edges are `x_B = q^(e1)`, `x_C = r^(e2)`, `y_C = p^(e3)`, with `x_A = p`, `y_A = q`, `y_B = r`. They give
    `ε_A τ(y_A) χ(e1) = ε_B τ(x_B)`, `ε_B τ(y_B) χ(e2) = ε_C τ(x_C)` and `ε_A τ(x_A) χ(e3) = ε_C τ(y_C)`.
  - Multiplying, and using `ε^2 = τ^2 = 1`, gives `σ(G) = +1` as a necessary condition. When it holds, `ε_A` is
    free and determines `ε_B` and `ε_C`.
  - The rerun shows the per-candidate values: `G_2` and `G_4` fail on all 8 triples, which is `σ = -1`. `G_1` and
    `G_3` pass on exactly 2, which is `σ = +1`.
- **Dimension 5 in characteristic 2.**
  - `W_X = [V, X]` is 4-dimensional, and a subspace containing `W_X` is `X`-invariant, since `X` acts trivially on
    `V/W_X`. So `V' = W_A + W_B + W_C` is `G`-invariant.
  - `W_A ∩ W_B ⊇ [V, E_AB]`, which is 3-dimensional, so `dim(W_A + W_B) <= 5`.
  - If `[V, E_BC] = [V, E_CA]`, that 3-dimensional space would be invariant under `<x_C, y_C> = C`, inside the
    irreducible `4`. That is impossible. So the two images are distinct, they span `W_C`, and `W_C <= W_A + W_B`.
  - Hence `dim V' in {4, 5}`, which is `lin4` or `lin5`.
- **Characteristic 7.**
  - `F_7^8 = 1 ⊕ 7` for `A_8`, and restricting to a Sylow 7-subgroup gives `F_7[C_7] ⊕ 1`. So by Krull--Schmidt, a
    7-element is one Jordan block on `7`.
  - Edge consistency makes the `A` and `B` modules free over `C_7`, hence projective.
  - For the principal 7-block of `A_7`: the defect group is cyclic, `N(P) = 7:3`, so `e = 3`, the Brauer
    characters are `1, 5, 10`, and `P(1) = 1 + 6` is the only projective indecomposable of dimension 7. The other
    blocks are simple projectives of dimensions 14, 14, 21 and 35.
  - So the modules are the permutation module, which the integral `N = 1` covers.
- **Characteristic 2, type 6 with factors `{6, 1}`.** On `A_7`, `F_2^7 = 1 ⊕ 6`, because
  `H^1(A_7, F_2^7) = H^1(A_6, F_2) = 0`. So the `B`-side parametrization by circulants is valid. The `C`-side enters
  only through traces, which see composition factors only. So `N = 1` covers every `{6,1}` structure at `C`.

## 3. Verdicts

| claim | verdict |
|---|---|
| `a7a7a8-triangle-candidates-no-4dim-char2-representation` | PASS: certificates reproduced, sign lemma and parametrization re-derived |
| `a7a7a8-triangle-candidates-no-small-linear-representation` | PASS at the checked steps: certificates reproduced; the `dim V' <= 5` and characteristic-7 steps re-derived |

**Recalled, not re-read.**
- The 2-, 3- and 5-modular irreducibles of `A_7` and `A_8` of degree `<= 7`.
- `H^1(A_7, 4) = H^1(A_7, 4*) = H^1(A_8, 4) = 0`.
- The `A_7` character degrees used in the Brauer tree count.

The node already lists these as recalled.

**Scope, unchanged.**
- These are exclusion certificates, exhaustive for the stated dimensions. They are not searches, and they say
  nothing about `PSL_d(q)` quotients of larger dimension.
- `hyperbolic-simple-triangle-group-without-finite-quotients` remains OPEN.
- Projective `μ_7`-twists are excluded only in characteristics 0, 7, 29 and 43, and in all but finitely many
  characteristics.
