# bh-verify-master, item 4: the golden–silver refutation and Labbé wall rigidity

Adversarial check by lane bh-verify-master, 2026-09-18, read on origin/main at 6481dbd30. Lane check,
not an external review.

**Verdict: PASS for both.** Trust points are listed at the end of each part.

## 4a. `v-times-golden-silver-wang-product-full-group-is-not-fp`

Dynamical input: `metallic-wang-shift-product-is-minimal-with-split-differences`, via route
`metallic-wang-product-minimality-and-row-faults-proof`.

**Part 1: finite type, freeness, minimality.** Correct.
- **Finite type.** Products of SFTs are SFTs.
- **Freeness.** It follows from aperiodicity of `Ω_1`.
- **Characters.** A character `(a,b,c,d)` trivial on `H` forces `aβ_1 + cβ_2 ∈ Z`. That is
  `a/2 + c + (a/2)√5 + c√2 ∈ Z`, so `a = c = 0`. Likewise `b = d = 0`.
- **Density.** By Kronecker, `H` is dense in `T^4`, so the product rotation is minimal.
- **Lemma 1.** Almost one-to-one extensions give a product that is minimal whenever the product of the
  bases is. The argument uses the dense invariant set `W_1 × W_2` of singleton-fibre points, which
  every closed invariant set must contain.

**Part 2: a two-row fault in `Ω_n`.** Correct. I re-derived all twelve affine forms of `Tile_n` from
the quoted definition of `Λ_n`.
- The top and bottom labels carry `{x_i}` with coefficient 1.
- The right and left labels carry it with coefficients `β^{-1}` and `β`, except for their first
  entries, which have no `x`-term.
- At `y = 0` those first entries equal `(j−1)β^{-1}` plus an integer, so they are integers only
  for `j = 1`.
- For `j ∉ {0,1}`, every form is a non-integer at `y ≡ 0` and depends continuously on
  `y = 1 − t`, since `jβ^{-1}` and `(j−1)β^{-1}` are not integers.
- Row 1: the first entry of the right label is `1` at `y = 0` and `⌊1 − t⌋ = 0` for
  `0 < t < β^{-1}`.
- The limit `c'` exists by compactness, and it differs from `c` exactly as claimed.

**Part 3: split differences.** Correct. The distance between the two fault rows is at least `m + 1`.

**Independent confirmation through the verified necessity theorem (item 1).** Split difference sets
give a noncommuting `D`-quantum family on `k²` as soon as the split distance exceeds `3D`:
- On a neighbourhood `N_D(Δ_2)`, conjugate the diagonal family `diag([u(q)=a],[v(q)=a])` by
  `T_0 = [[1,1],[0,1]]`, and leave it diagonal elsewhere.
- **(Q2)** holds because any pair of sites at distance `≤ 2D` in different regimes has one scalar
  site.
- **(Q3)** holds because every window of diameter `2D` has all its nonscalar sites in one regime.
- **Noncommutation.** `diag(1,0)` and `T_0 diag(1,0) T_0⁻¹ = [[1,−1],[0,0]]` do not commute.

So `X` is not `D`-quantum rigid for any `D`. Part 1 of
`fp-v-times-subshift-full-groups-force-quantum-rigidity` then gives the refutation directly, without the
older connected-differences node.

**Scope** (as the node says): this refutes only the universal P2. It does not touch
`free-minimal-z2-sft-is-quantum-rigid`, which is existential.

**Trust points:**
- Labbé's Theorems 1.1, C, D and F(ii) (arXiv:2403.03197v3), quoted verbatim;
- Kronecker's theorem.

## 4b. `labbe-shift-is-wall-rigid`

This concerns the 19-tile shift `Ω_U`, not the metallic `Ω_n`. Proof: artifact
`labbe-shift-wall-rigidity-2026-09-13.md`, Sections 1–3.

- **Lemma 1 (atoms vs letters).** Correct.
- **Lemma 2 (generic limits; constant side on exact hits).** Correct. The side is fixed by the sign of the
  normal component of `y_k − x`.
- **Lemma 3 (no finite 2D-clusters).** Correct.
  - `T_3` is valid, since `r = 1` and the ring `N_(2D)(F) \ F` agrees.
  - Independent flips at syndetic far-apart occurrences give positive entropy.
  - That contradicts `h_top = 0`, which follows from unique ergodicity with a rotation measure and the
    variational principle.
- **Lemma 4.2.** `mα ≡ s(m)(1,−φ)`, using `φ^{-2} = 2 − φ = 1 − φ^{-1}`. Correct. So the whole
  Z²-orbit lies on one leaf of direction `(1,−φ)`.
- **Case A (`|v| ≥ ε_0`).** Correct.
  - A distinct translate `P_a − v` gives an open ball `U_v` with `t` and `t+v` in the interiors of
    distinct atoms.
  - The radius is lower semicontinuous and positive, so it is bounded below on the compact set
    `{|v| ≥ ε_0}` of the torus.
  - Returns to `U_v` are `G`-dense, by bounded gaps coordinatewise.
  - A `G`-dense subset of Z² is `(2G+1)`-connected.
- **Case B (`0 < |v| < ε_0`).** Correct at the level written.
  - `ε_0 < ℓ_min/(4C')` makes each core interval longer than `ℓ_min/2`.
  - Every difference point lies on a sheet with offset in `(0, v⊥)` that carries core points.
  - Sheets of distinct lattice directions always cross, so the core points are connected at scale
    `max(G_1, 2G_2)`.
  - The general-pair limit argument keeps chains inside finite boxes, and the constant does not depend
    on `v`.
- **Case C (`v = 0`).** Correct.
  - Each segment has at most one exact-hit sheet: for rows, `x_2 + n_2α ≡ h_σ` has at most one
    solution. So `B_par` is finite.
  - Lemma 3 puts a full line in every component.

**Trust points:**
1. The partition geometry of `P_U` (segment directions and vertex coordinates) was read from the
   vector content of Labbé's figure, not from a stated theorem.
2. The bounded-gap constants of Lemma 5 come from the three-distance theorem, recalled, with the
   irrational-direction strip geometry treated at outline level.
3. Injectivity of the coding on generic points (`lem:tiling-one-to-one`).

None affects the logic; items 1–2 affect only the values of the constants.

**Consistency with 4a.** Metallic `Ω_n` row faults are full rows, so they are connected, and the split
arises only in the product. Labbé's `Ω_U` has fault lines in four directions, which cross. There is no
conflict.

## Lesson for general BH

Wall rigidity (first-order) is a geometric crossing property of fault networks, and it genuinely
separates examples:
- the golden–silver product fails it through independent parallel faults;
- Labbé's `Ω_U` has it through faults in four directions, including an irrational one.

The open crux for Z² is therefore strictly higher-order: `J_D = 0` beyond `J_D = J_D²`. Any positive
proof must use more than the crossing of faults.
