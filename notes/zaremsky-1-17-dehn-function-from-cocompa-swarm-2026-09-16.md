# Zaremsky 1.17 (Dehn function from cocompact action data): swarm lane, 2026-09-16

**Target:** `zaremsky-1-17-dehn-function-from-cocompact-action-data`, locked for
this lane with a 180-minute TTL.

**Holes attacked:**

- `some-action-violates-dehn-bound-without-finite-index-faces`, searching for
  counterexamples among groups with large Dehn function;
- `dehn-bound-from-action-data-without-finite-index-faces`, via a bounded-twist
  lemma.

**Result:** a calibration theorem (below). The root remains open.

## 1. Setup

**Setting (S)** is that of the root. `G` acts cellularly, cocompactly and
without inversions on a simply connected simplicial complex `X` with
`δ_X < ∞`. Vertex stabilizers are finitely presented and edge stabilizers
finitely generated. Put `dist_X(n) = max_{dim σ ≤ 2} dist^G_{G_σ}(n)`.

The bound under test is

```text
(UB)  δ_G(n) ≼ R_X(n) := δ_X(n) · max_v δ_{G_v}( dist_X‾( δ_X(n) ) ).
```

**Normalization.** Read literally, (UB), and Theorems B and C of Llosa
Isenrich–Weis, are degenerate:

- `ℤ²` is an HNN extension of `ℤ`, whose presentation `⟨a | ⟩` has
  `δ ≡ 0`, so Theorem B would give `δ_{ℤ²} ≼ 0`;
- a free cocompact action has `dist_X ≡ 0`, so `R_X ≡ 0`.

The area estimates in §3.1 of the paper have the form
`δ_{G_v}(n + edist_X(Dn))`. I therefore work under normalization (N): replace
every Dehn function `δ` by `max{δ(n), n}` and `dist_X(n)` by
`max{dist_X(n), n}`. Anyone adjudicating a claimed counterexample has to fix
such a convention first. A counterexample that exploits a degenerate
convention is worthless.

## 2. External gate (literature status, checked 2026-09-16)

- **Llosa Isenrich–Weis**, *A Brown Theorem for Dehn functions of graphs of
  groups*, arXiv:2608.07191v1 (7 August 2026). The PDF was fetched and the text
  extracted locally.
  - Theorems B (trees) and C (`[G_e : G_σ] < ∞`) are as imported in
    `llosa-isenrich-weis-dehn-bound-for-cocompact-actions`. The introduction
    says the question "was raised by Zaremsky [Zar26, Problem 1.17]. We give an
    affirmative answer if X is 1-dimensional."
  - §2.1 gives the definitions used here: `≼` with the `+Cn + C` term;
    admissible (singular combinatorial) maps and `Vol` in Definition 2.2;
    `FVol` and `δ_X` in Definition 2.3.
  - §5 contains the applications: 5.1 group extensions (monodromy distortion,
    Definition 5.4, Theorem 5.6, Lemma 5.7 `Mon ≼ dist`, Corollary 5.8
    attributed to [Con95], Example 5.10 on the Sol extension), and 5.2
    amalgams of nilpotent groups along cyclic subgroups (Hidber; Corollary
    5.11). All of these go through trees or through Theorem C, where face
    stabilizers have finite index in edge stabilizers.
  - Nothing in the paper treats infinite-index faces.
- **Sauer–Weis**, *Polynomial homological Dehn functions from non-proper
  actions*, arXiv:2606.25897v1 (24 June 2026). The PDF was fetched and the text
  extracted locally.
  - Theorem A gives *qualitative* polynomiality of homological Dehn functions.
    It assumes that the chain complex is `(d−1)`-`EΓ`-connected (for example
    when `X^(d)` is locally finite and the complex's `FV` is polynomial), that
    stabilizers are of type `FP_{d−k}` with polynomial `FV`, and that they are
    finitely generated and at most polynomially distorted.
  - It gives no explicit formula, so it does not answer (UB). Its
    connectedness hypothesis is aimed at the locally finite regime, while the
    open case of (UB) is non-locally-finite in degree 2.
  - The EW-type Theorem B there (graphs of groups) is qualitative as well.
- **Zaremsky**, *Some open problems* (version of July 12, 2026), Problem 1.17.
  The verbatim wording is as recorded in the root node; I did not re-fetch it
  this session.
- **Epstein et al.** (1992, for `δ_Sol ≃ e^n`) and **[Con95]/[Bri93]/[BC98]**,
  as cited inside the Llosa Isenrich–Weis paper, were not consulted directly
  (unverified). The new proof uses only `δ_G ≼ e^n`, proved from scratch.
- **Search limits.** My web-search budget ran out early in the session, so a
  broad search for follow-ups (a v2 of arXiv:2608.07191, or other 2026
  preprints on non-locally-finite complexes of groups) could not be done. As
  far as checked, the root is open.

## 3. What was proven

**Theorem** (`sol-lattice-actions-satisfy-the-dehn-action-bound`, route
`sol-lattice-dehn-action-bound-proof`, full proof in
`research/artifacts/sol-lattice-dehn-action-bound-2026-09-16.md`). For
`G = ℤ² ⋊_M ℤ` with `M ∈ GL_2(ℤ)` hyperbolic, every action in (S) satisfies
(UB) under (N).

The proof is a case split:

- **`δ_G ≼ e^n`**, elementary.
- **Subgroup dichotomy.** A subgroup meeting `ℤ²` nontrivially lies in `ℤ²` or
  has finite index.
- **Case 0: a vertex stabilizer of finite index.** Its Dehn function is
  `≃ δ_G`.
- **Case 1: a nontrivial vertex stabilizer inside `ℤ²`.** Fiber elements have
  `ℓ_G(z^m) = O(log m)`, via a two-sided greedy digit expansion in `ℤ[λ]`
  embedded as a lattice in `ℝ²`. So `dist_X ≽ e^n`.
- **Case 2: all vertex stabilizers trivial or `⟨w t^k⟩` with `k ≠ 0`.**
  - Each nontrivial stabilizer has a unique fixed point for the
    area-preserving affine action `t ↦ M` plus translations, so there is an
    equivariant `f : X^(0) → ℝ²`.
  - The signed-area 1-cochain `A(x, y) = ½ det(f(x), f(y))` gives
    `FVol_X(γ) ≥ |A(γ)| / C_X`. An admissible map is cellular: nonsingular
    2-cells push forward to `±σ`, singular ones to `0`.
  - `A(γ_w)` differs from the shoelace area of the orbit polygon by `O(|w|)`.
  - For `w_n = [t^n a t^{−n}, t^{−n} a t^n]` the orbit polygon has area exactly
    `det(M^n e_1, M^{−n} e_1)` for every base point.
  - So `δ_X ≽ e^n`.

**Verification.**
`experiments/zaremsky-1-17-dehn-function-from-cocompa-swarm-2026-09-16/sol_orbit_polygon_area.py`
(output `.out`, "ALL CHECKS PASSED") checks:

- the base-point independence and the exact value of the polygon area, in
  exact rational arithmetic for three matrices (one with determinant `−1`),
  `n ≤ 10`, with random rational base points;
- `det(M^k − I) ≠ 0` for `|k| ≤ 30`;
- the digit expansion numerically for `m ≤ 10¹²`: word length / `log m` stays
  between about 7 and 23.

**What it means for the graph.** Sol lattices are the model groups whose
exponential Dehn function comes from distortion. No action of one, on any
complex in (S) and whatever its face stabilizers, is a counterexample. A
counterexample has to hide the growth of `δ_G` from `δ_X`, from all stabilizer
distortions and from the vertex Dehn functions at once. For Sol that is
impossible, because the invariant area form transfers to `δ_X` as soon as
stabilizers have fixed points. I added no route into the root, since this is a
calibration only.

## 4. Approaches tried and where each dies

1. **Bounded-twist filling lemma (for the "yes" side).** By part 2 of the
   2026-09-13 artifacts, (UB) reduces to bounding the face-collapse detours of
   some filling of area `≼ δ_X(n)`. With trivial face stabilizers, these are
   the twists along interior edges of the X-diagram.
   - For a fixed X-diagram, the twist on an interior edge between faces over
     `σ, σ'` sharing `e` is a well-defined double coset in
     `G_σ \ G_e / G_{σ'}`. It is intrinsic to the diagram, and re-choosing lifts
     gives no freedom to shorten it.
   - So a proof would have to pick among X-fillings of comparable area the ones
     with short twists. Nothing in `(δ_X, δ_{G_v}, dist_X)` controls that
     choice.
   - **Dies:** no mechanism found. This remains the open step of
     `dehn-bound-from-action-data-without-finite-index-faces`.
2. **Thicken or cone `X` to force finite-index faces, then apply Theorem C.**
   Examples: subdivide each 2-simplex with a free central vertex, or add strips
   along edges so that the new 2-cells have stabilizers of finite index in the
   new edge stabilizers.
   - The new complex `X'` does satisfy the hypothesis of Theorem C.
   - But `δ_{X'}` has to pay for the twists that `X` got for free: loops in `X'`
     that lie over short `X`-loops need area comparable to the twist lengths.
   - **Dies:** circular. `δ_{X'}` is not bounded in terms of `δ_X` and the
     stabilizer data.
3. **Counterexample search among polycyclic groups with exponential Dehn
   function.** For hyperbolic Sol lattices, every action in (S) satisfies (UB)
   (Section 3).
   - **Dies:** by that theorem. The mechanism "exponential area hidden from the
     action data" is excluded for them.
4. **Heisenberg group `H_3` (nilpotent, `δ ≃ n³`).**
   - If some cell stabilizer (dimension ≤ 2) contains a nontrivial central
     element, then it is abelian (a non-abelian subgroup of `H_3` has finite
     index, a case that is fine anyway) and the central element is undistorted
     in it but quadratically distorted in `G`. So `dist_X ≽ n²` and
     `R_X ≽ n · n² = n³`.
   - Otherwise every stabilizer of dimension ≤ 2 is trivial or infinite cyclic
     and non-central. Any `ℤ²` in `H_3` contains central elements. Non-central
     elements are undistorted, so `R_X ≃ δ_X²`, and (UB) needs
     `δ_X ≽ n^{3/2}`.
   - A free action has `δ_X ≃ n³`, which is fine.
   - Coning off the cosets of `⟨x⟩` in the Cayley complex (stabilizers the
     conjugates of `⟨x⟩`) gives a simply connected complex. There `x^p` has
     length 2, so `[x^p, y][x^{p'}, y][x^{p+p'}, y]⁻¹` (`= z^p z^{p'} z^{−p−p'}`)
     is a loop of length 18 in `X`. A `y`-corridor count suggests its filling
     area is unbounded in `p, p'`, i.e. `δ_X(18) = ∞`, so this complex is not
     admissible in (S). This is a sketch, not written in full; treat it as
     unverified.
   - The area-transfer trick of Section 3 does not apply: cyclic non-central
     stabilizers act on the abelianization plane by translations and have no
     fixed points. An invariant for the central extension (for example the
     `z`-content of a loop measured through the cone vertices) would be the
     analogue.
   - **Dies:** the lower bound `δ_X ≽ n^{3/2}` is neither proved nor refuted.
     This is the first open calibration. It is either a place to look for a
     counterexample (an `H_3`-complex in (S) with cyclic non-central
     stabilizers and `δ_X ≪ n^{3/2}`) or the next test of the area-cocycle
     principle.
5. **Nonpositively curved triangles of groups** (Gersten–Stallings angle
   condition on the links of the three vertex groups).
   - The developments are CAT(0), and at each corner the two edge subgroups
     behave like a "large girth" pair inside the vertex group. That keeps the
     corner coarse-intersection function `κ_X` of part 1 heuristically linear.
   - **Dies (as a counterexample source):** these look like tame cases, not
     candidates. Not proved in general.
6. **General area-cocycle principle.** Case 2 of the theorem generalizes as
   follows: if `G` acts on `ℝ²` by area-preserving affine maps and every
   vertex stabilizer fixes a point, then `δ_X(Ln) ≥ (orbit-polygon area of
   words of length n − O(n)) / C_X`.
   - **Dies (as a proof of (UB)):** this bounds `δ_X` from below only when
     `δ_G` is witnessed by such an invariant area form and the stabilizers have
     fixed points. It gives nothing for groups without such structure, or with
     translation-like stabilizers (`H_3` above).

## 5. Suggested next targets

- **`H_3` with cyclic non-central stabilizers.** Build an admissible complex
  and compute `δ_X`, or prove `δ_X ≽ n^{3/2}` using an invariant of the central
  extension. A complex with `δ_X ≼ n^{3/2 − ε}` would refute (UB) in the form
  of the root (route `zaremsky-1-17-by-no`).
- **More general calibrations.** Lattices in other solvable Lie groups with a
  semisimple part acting with fixed points, such as higher-rank `ℤ^k ⋊ ℤ^l`,
  should satisfy (UB) by the same fixed-point transfer. The counterexample
  search should move to groups whose Dehn function is not witnessed by an
  invariant 2-form, e.g. nilpotent central extensions.

## 6. Files of this lane

- `research/sol-lattice-actions-satisfy-the-dehn-action-bound.md` (claim)
- `research/sol-lattice-dehn-action-bound-proof.md` (route, `requires: []`)
- `research/artifacts/sol-lattice-dehn-action-bound-2026-09-16.md` (proof)
- `experiments/zaremsky-1-17-dehn-function-from-cocompa-swarm-2026-09-16/sol_orbit_polygon_area.py`
  and `sol_orbit_polygon_area.out`
- this note

## Referee (2026-09-16)

**Checked.**

- **Every step of the artifact.**
  - §1: irreducibility, irrationality of `λ^k`, and the ring map.
  - §2: Lemma 1. The length induction `|v_j| ≤ K^j Σ_{i≤j}|u_i|` holds and the `t`-prefix freely reduces.
  - §3: Lemma 2.
  - §4: Lemma 3, including the digit bounds `|c_j|, |d_j| ≤ B`, the bounds on `|s|` and `|s'|`, and the Horner words.
  - §5: Lemma 4. A singular combinatorial map is cellular, nonsingular 2-cells have degree ±1 on their image cell, singular ones have degree 0, and `A(∂c) = Σ n_σ A(∂σ)`.
  - §6: Lemma 5, the telescoping identity.
  - §7: Lemma 6, the `T_1/T_2/T_3` split, including `d = −1`.
  - §8: the case split is exhaustive, and the (N)-dependent inequalities in Cases 0–2 hold.
- **Mistakes found.** None in the mathematics.
- **Normalization (N).** It is needed; without it `R_X` degenerates for free actions. It agrees with the convention already used by the established node `cocompact-action-data-do-not-determine-dehn-function`. The claim states it explicitly, so this is not a hidden change of the root's (UB).
- **Independent recomputation.** Lemma 6 was recomputed with a symbolic base point `p_0 = (x, y)` in sympy, for six hyperbolic matrices including two with determinant −1 and one with negative trace, `n ≤ 5`. The difference `sh(P_{w_n}) − det(M^n e_1, M^{−n} e_1)` is identically `0`. Files: `experiments/zaremsky-1-17-dehn-function-from-cocompa-swarm-2026-09-16/referee_lemma6_symbolic.py` and `.out`. The solver's script was also rerun and its output agrees.
- **Citations.** Both arXiv abstract pages were fetched on 2026-09-16:
  - arXiv:2608.07191 is Llosa Isenrich–Weis, "A Brown Theorem for Dehn functions of graphs of groups", v1 of 7 Aug 2026, the only version. Its abstract says it answers Zaremsky's question for trees and for finite-index faces.
  - arXiv:2606.25897 is Sauer–Weis, "Polynomial homological Dehn functions from non-proper actions", v1 of 24 Jun 2026.
  - I could not run a further web search because the search budget was exhausted, so the status of the root was not rechecked beyond these pages.
- **Duplicates.** `bin/cairn search --similar` finds no duplicate. The claim routes into nothing, and the root keeps its no-`requires: []` rule.

**Changed.**

- **Case 0 citation.** Case 0 relies on quasi-isometry invariance of Dehn functions. This is now cited as classical (Alonso 1990, not re-read), in both the artifact and the route.
- **Claim wording.** The claim now points to the repo's existing convention for (N), and notes that for `det M = −1` the group is only virtually a Sol lattice.

**Verdict.** Sound. The direct proof is complete under the stated normalization and lands, with the minor fixes above. The root and both holes stay open. The `H_3` discussion in §4 of this note is heuristic, and its coning example is flagged unverified.
