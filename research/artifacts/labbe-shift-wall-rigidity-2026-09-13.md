# Labbé's shift is wall-rigid

Lane `ex2-labbe-quantum-rigidity`, 2026-09-13. Unreviewed. Part 2; part 1 is
`research/artifacts/quantum-rigidity-walls-and-commutator-ideal-2026-09-13.md`. It supports
`labbe-shift-is-wall-rigid` and `labbe-shift-is-a-toral-rotation-coding`.

## 0. Inputs, read from the source (arXiv:1903.06137, TeX on MSI, `common-content.tex`)

- **Rotation (lines 522–528).** On `T^2 = R^2/Z^2`, `R_U^n(x) = x + φ^(-2) n`, with `φ = (1+√5)/2`.
- **Theorem `thm:OmegaU-partition` (lines 539–559).** The Wang shift `Ω_U` has five properties:
  - (i) `X_(P_U, R_U)` is minimal, aperiodic and equal to `Ω_U`;
  - (ii) `P_U` is a Markov partition for `(T^2, Z^2, R_U)`;
  - (iii) the rotation is the maximal equicontinuous factor;
  - (iv) the fiber cardinalities of the factor map are `{1, 2, 8}`;
  - (v) `Ω_U` is strictly ergodic and measure-isomorphic to the rotation with Haar measure.
- **Definition `def:Markov` (line 1089).** A Markov partition gives a symbolic representation
  (`def:symb-repr`): for every `w`, `∩_n cl D_n(w)` is one point, called `f(w)`.
- **Lemma `lem:closure-of-tilings` (line 1284).** `X_(P,R)` is the closure of the codings of points whose
  orbits avoid `∂P`.
- **Proposition `prop:factor-map` (line 1427).** `f` is a factor map.
- **Geometry of `P_U` (read from the vector figure `article3_partitionU.pdf`).** The content stream draws
  segments in the frame `[0, 85.04042]^2`, which is the square `[0,1]^2`. All vertex coordinates lie in
  `{0, φ^(-3), φ^(-2), φ^(-1), 2φ^(-2), 1}`.
  - Every segment has direction `(1,0)`, `(0,1)`, `(1,-1)` or `(1,-φ)`.
  - Each direction occurs away from the frame: `(φ^(-3), φ^(-1))–(φ^(-2), φ^(-1))`,
    `(φ^(-2), 0)–(φ^(-2), φ^(-2))`, `(φ^(-2), φ^(-1))–(φ^(-1), φ^(-2))` and `(0, 1)–(φ^(-3), φ^(-1))`.

Write `α = φ^(-2)`, `P = P_U`, and `f : Ω_U -> T^2`. Subdivide segments at crossings, so that segments meet
only at endpoints. Let `ℓ_min` be the least segment length. Adjacent atoms across a segment are distinct.

## 1. Three lemmas about configurations

**Lemma 1.** Let `T ∈ Ω_U` and `x = f(T)`.
1. If `x + nα ∈ int P_a`, then `T(n) = a`.
2. If `T(n) = a`, then `x + nα ∈ cl P_a`.

*Proof.* `x ∈ cl D_k(T) ⊆ cl R^(-n) P_(T(n))` gives 2. For 1: if `T(n) = b != a`, then `x + nα` lies in
`int P_a ∩ cl P_b`, which is empty. QED

**Lemma 2 (limits and consistent sides).** Every `T ∈ Ω_U` is a pointwise limit `Φ(y_k) -> T`, with
`y_k -> f(T)` and every `y_k` generic (orbit avoiding `∂P`). Let `σ` be a segment and
`E_σ(x) = {n : x + nα ∈ σ, x + nα not an endpoint}`. Then `T` reads the same side of `σ` at every
`n ∈ E_σ(x)`.

*Proof.* The limit is Lemma `lem:closure-of-tilings` together with continuity of `f`.
- At `n ∈ E_σ(x)`, for large `k`, `Φ(y_k)(n)` is the atom on the side of `σ` given by the sign of the
  component of `y_k - x` normal to `σ`. That sign is the same for all such `n`.
- Convergence at one `n` forces the sign to be eventually constant. QED

**Lemma 3 (no finite clusters; the predecessor's Proposition 4).** Let `D >= r = 1` and `T_1, T_2 ∈ Ω_U`.
Every `2D`-component of `Δ = Δ(T_1, T_2)` is infinite.

*Proof.*
1. **The modified tiling.** Let `F` be a finite component. `T_1 = T_2` on `N_(2D)(F) \ F`. Let `T_3` agree
   with `T_2` on `F` and with `T_1` elsewhere. Every `r`-ball meeting `F` lies in `N_(2D)(F)`, where `T_3`
   reads `T_2`. So `T_3 ∈ Ω_U`, and it differs from `T_1` exactly on `F`.
2. **Syndetic occurrences.** By minimality, the pattern of `T_1` on `N_(2D)(F)` occurs syndetically.
3. **Independent flips.** Writing `T_1|F` or `T_3|F` independently at `c n^2` far-apart occurrences in an
   `n`-box gives `2^(c n^2)` patterns. So the entropy is positive.
4. **Contradiction.** By (v) the unique invariant measure is isomorphic to a rotation, so it has entropy `0`,
   and the variational principle gives `h_top = 0`. QED

## 2. Sheets

Each direction `u` has a *lattice direction*: `(1,0) -> (1,0)`, `(0,1) -> (0,1)`, `(1,-1) -> (1,-1)`, and
`(1,-φ) -> (φ, 1)`.

**Lemma 4 (exact transport).**
1. For `e ∈ {(1,0), (0,1), (1,-1)}`, `(ke)α = kα e`.
2. For every `m ∈ Z^2`, `mα ≡ s(m)(1,-φ)` mod `Z^2`, with `s(m) = m_2 - m_1/φ`.

*Proof of 2.* First coordinate: `m_1 φ^(-2) = m_1 - m_1φ^(-1)`, which is `≡ s(m)` mod `1`. Second
coordinate: `m_2(2 - φ) ≡ -m_2 φ`, and `-φ s(m) = -φ m_2 + m_1 ≡ -φ m_2`. QED

So translating `n` along the lattice direction moves `x + nα` along a line of direction `u`.
- For rational `u`, the internal point moves around a closed circle, by an irrational rotation.
- For `u = (1,-φ)`, the internal point moves along one dense leaf. The lattice points whose parameter `s`
  lies in a window form a strip in direction `(φ, 1)`.

A *sheet* of `σ` through `n_0` is the set of `n` obtained by such a translation. Along a sheet the transverse
offset of `x + nα` from the line of `σ` is constant.

**Lemma 5 (gap constants).** There are constants `G_1, G_2, M` depending only on `P`:
1. **Along a sheet.** The points of a sheet whose position along `σ` lies in a fixed sub-interval of `σ` of
   length `>= ℓ_min/2` are `G_1`-dense in the sheet, and the sheet passes within `G_1` of them.
2. **Crossing.** Sheets of distinct lattice directions intersect as subsets of `R^2`, and each has such
   points within `G_2` of the intersection.
3. **Spacing.** For an offset window of length `μ`, consecutive parallel sheets with offsets in the window
   are at distance `<= M/μ`.

*Proof.* Returns of the rotation by `α` (or by `α` along the leaf) to an interval of length `λ` have gaps
`<= C/λ`. This is the three-distance theorem for the badly approximable `φ`; it is recalled, not re-derived.
Part 2 is plane geometry for non-parallel lines and strips. QED

## 3. Theorem W

**Theorem W.** There is `D_0` such that `Ω_U` is `D`-wall-rigid for every `D >= D_0`.

Fix `T_1, T_2`, put `x_i = f(T_i)`, and let `v ∈ [-1/2, 1/2)^2` represent `x_2 - x_1`. Choose `ε_0` smaller
than `ℓ_min/(4C')` and than half the distance from the middle part of any segment to all other segments,
where `C'` depends on the angles between segments.

**Case A: `|v| >= ε_0`.**
1. **An open set of disagreement.** If `P_a + v = P_a` for every atom, the codings of `x` and `x + v` would
   coincide for generic `x`, contradicting injectivity (Lemma `lem:tiling-one-to-one`).
   - So some polygon `P_a` differs from `P_a - v`, and the difference has interior. This gives a ball `U_v`
     such that for `t ∈ U_v`, `t` and `t + v` lie in the interiors of distinct atoms. Atoms are open and
     pairwise disjoint.
   - The radius is `>= ρ_0 > 0` uniformly on `{|v| >= ε_0}`, by compactness and lower semicontinuity of the
     largest such radius.
2. **Density.** By Lemma 1, `x_1 + nα ∈ U_v` implies `T_1(n) != T_2(n)`. Returns to `U_v` are `G_A`-dense,
   by Lemma 5 in each coordinate. So `Δ` is `G_A`-dense, and hence `(2G_A + 1)`-connected.

**Case B: `0 < |v| < ε_0`.**
1. **Core parallelograms.** For a segment `σ` not parallel to `v`, let `core(σ)` be `σ` minus the
   `C'|v|`-neighbourhoods of its endpoints, and `K_σ(v) = {q - s v : q ∈ core(σ), 0 < s < 1}`.
   - By the choice of `ε_0`, points of `K_σ(v)` lie in the interior of one atom adjacent to `σ`, and their
     `v`-translates in the interior of the other.
   - So `x_1 + nα ∈ K_σ(v)` gives `n ∈ Δ`, by Lemma 1. Call these *core points*.
2. **Generic pairs.** Suppose first that `x_1` and `x_1 + v` are generic, and `x_1` avoids the orbits of the
   lines `p + Rv` through vertices `p`. For `n ∈ Δ`, the segment `[t, t+v]` (`t = x_1 + nα`) crosses `∂P` at
   an interior point of a segment `σ` not parallel to `v`.
   - So `n` lies on a sheet of `σ` with offset strictly inside `(0, v⊥)`.
   - That sheet carries core points within `G_1` (Lemma 5.1).
3. **The network.** At least three of the four directions are not parallel to `v`, giving at least two
   distinct lattice directions of core sheets.
   - Sheets of distinct directions cross within `G_2` (Lemma 5.2), and any two parallel sheets are both
     crossed by a sheet of another direction.
   - So the core points form one `max(G_1, 2G_2)`-connected set, and `Δ` is `G_B`-connected with
     `G_B = G_1 + max(G_1, 2G_2)`.
4. **Local paths.** In addition, since the mesh is `<= M/(c|v|)` (Lemma 5.3), two points of `Δ` at distance
   `ρ` are joined inside `Δ` within the ball of radius `ρ + M'/|v|`.
5. **General pairs.** By Lemma 2, `T_1 = lim Φ(y_k)` and `T_2 = lim Φ(y'_k)`, so `y'_k - y_k -> v`.
   - `Φ` is locally constant on finite boxes at generic points. So we may first move `y'_k` to a generic point,
     and then move `y_k` off the countably many lines through `y'_k` and the points `p - nα`. This keeps both
     limits and makes each pair generic as in step 2.
   - For each finite box `B`, `Δ ∩ B = Δ_k ∩ B` for large `k`.
   - Take `n, n' ∈ Δ` and a box containing the ball of radius `|n - n'| + 2M'/|v|` around `n`. For large `k`,
     the chain of step 4 in `Δ_k` lies in that box, so it is a chain in `Δ`.
   - Hence `Δ` is `G_B`-connected. The constant `G_B` does not depend on `v`; only the size of the box does.

**Case C: `v = 0`.**
1. **Where differences can be.** By Lemma 1, `Δ ⊆ ∪_σ E_σ(x) ∪ V`, where `V` is the set of `n` with
   `x + nα` a vertex. `V` has at most one element per vertex, because the action is free.
2. **Full lines.** By Lemma 2, on each `E_σ(x)` the two tilings read constant sides. So `Δ ∩ E_σ(x)` is empty
   or all of `E_σ(x)`, a *full line*: `G_1`-dense along its sheet (Lemma 5.1).
3. **Components.** By Lemma 3 every component of `Δ` is infinite, so it contains a full line.
4. **Connecting the lines.**
   - Full lines of distinct directions come within `G_2`.
   - For a fixed `x`, parallel exact-hit sheets of two segments sit at an offset determined by the geometry.
     For example, for rows `(n_2 - n'_2)α ≡ h_σ - h_(σ')` has at most one solution. So such offsets are
     bounded by a constant `B_par`.
   - Hence `Δ` is `G_C`-connected with `G_C = max(G_1, G_2, B_par + G_1)`.

**Conclusion.** Take `D_0 >= 1` with `2D_0 >= max(2G_A + 1, G_B, G_C)`. QED

## 4. Consequences, via part 1

For `D >= D_0`, over any field `k`:
- **First order.** The commutator ideal of Labbé's local tiling algebra satisfies `J_D = J_D^2`. Every family
  on `k^2`, and every finitely filtered family with commuting quotients, commutes.
- **Finite dimensions.** Every noncommuting finite-dimensional family over an algebraically closed field has
  a composition factor of dimension `>= 3`. So does every periodic quantum tiling of Labbé's tiles at such a
  scale.
- **Reduction.** `labbe-wang-shift-crossed-product-is-finitely-presented` is equivalent to `J_D = 0` for some
  `D`. No first-order (extension) certificate can refute it.

## 5. Remarks (heuristic, not established)

- **Two first-order invariants separate here.** Labbé's shift has fault lines in four directions, one of them
  irrational (`(φ,1)`). Across a fault, two tilings agree on both sides, so neither half-plane determines
  the tiling in those directions.
  - For a group shift, antipodal half-plane indeterminism plus superposition produces walls. That is the
    analogue of the Bieri–Strebel doubling that makes non-tame metabelian groups infinitely presented.
  - Labbé's shift has no superposition, and no walls. Its quantum rigidity is exactly the question which of
    the two invariants governs finite presentation of tiling algebras.
- **No permutive recoding.** A triangle-permutive SFT should be expansive off the three side directions of
  its triangle (not checked). The four nonexpansive directions of `Ω_U`, including the irrational one, would
  then rule out every triangle-permutive recoding.
- **Constant-frame regions.** A thick half-strip of agreement forces equal torus points: the orbit along a
  half-strip in a non-fault direction is dense. So in a noncommuting family for `Ω_U`, any region where the
  eigen-decomposition is constant and contains a half-strip carries configurations from one fibre. The
  family cannot contain two such regions carrying different torus points. This constrains dimension `>= 3`
  mechanisms, but is not a proof.
