# Zaremsky 1.17: the lifted complex without finite-index faces (part 2)

Lane z1-17-dehn-cocompact, 2026-09-13. Unreviewed. Part 1:
`research/artifacts/zp-dehn-cocompact-face-collapse-2026-09-13.md`.
Source: arXiv:2608.07191v1, pp. 10–16 (the proof of Theorem C ends on p. 15;
Remark 3.7 extends it to polyhedral 2-complexes).

## 1. Simple connectivity and the exact cost, with no hypothesis on faces

Setting (S) of the root, with `X̂ → X` built as in Remark 2.22 of the paper:
vertex fibers `EG_v` (1-connected, since `G_v` is finitely presented), edge
fibers `EG_e × e` (connected, since `G_e` is finitely generated), and a
`G_σ`-orbit of hexagonal disks per 2-cell `σ`.

**Lemma 1 (face collapse, general).** Lemma 3.4 of the paper holds for every
2-cell `σ ⊃ e`, with `μ_1` a shortest path in `EG_e` from `γ(0)` to the image of
`EG_σ^(0)`. Write `c = ℓ(μ_1) = d_{EG_e}(γ(0), ψ_{e,σ}(G_σ))`. The homotopy
then has at most `c + 1` 2-cells and lengthens the loop by at most `2c + 4`.
*Proof.* Only the choice of `μ_1` used `[G_e : G_σ] < ∞`. A path to the image
exists because `EG_e` is connected, and the parallel translation, the disk and
the length count are unchanged.

**Corollary 2.** `X̂` is simply connected and `G` acts on it freely and
cocompactly, so `δ_G ≃ δ_{X̂}` in all of (S). *Proof.* Proposition 3.6 with
Lemma 1 turns any loop into one whose projection has a tree van Kampen
diagram, and Theorem 3.3 fills that. Freeness and cocompactness hold because
the disks over the `G`-orbit of `σ` form `G ×_{G_σ} G_σ ≅ G`.

**Corollary 3 (accounting).** Take a loop of length `n` in `X̂`, a van Kampen
diagram of its projection with area `A`, and a collapse sequence with detours
`c_1, …, c_A`. The loop has a filling in `X̂` with at most

```text
Σ_i (c_i + 1) + m · ( max_v δ_{G_v}( m + edist_X‾(D m) ) + edist_X(D m) ),
m = n + Σ_i (2 c_i + 4),
```

2-cells. When every `c_i ≤ C(X)` this is the paper's bound. So (UB) in general
is equivalent, up to the shape of the formula, to bounding the detours `c_i`
for some filling of area `≼ δ_X(n)`.

## 2. What the detours measure

Assume trivial 2-cell stabilizers, the simplest case beyond the paper. Then
each 2-cell carries exactly one disk, and the detour at a face meeting the
current loop along `e` is the `G_e`-distance from the loop's position to that
disk. Across an interior edge `e` of the diagram shared by 2-cells `σ` and
`σ' = hσ` (`h ∈ G_e`), the disks' positions in `EG_e` differ by `h` (by
equivariance), so the diagram itself forces a mismatch `≈ |h|_{G_e}`.

Around an interior vertex `w` of the diagram the faces form a cycle in the
link `Lk(w)`, an infinite graph with finitely many `G_w`-orbits. The mismatches
`h_1, …, h_k` along that cycle lie in edge stabilizers inside `G_w` and
multiply to a bounded element. So twists are relations in `G_w` among elements
of edge stabilizers, and a diagram of small area can carry huge twists. In
`G_w = ℤ²` with edge stabilizers `⟨x⟩` and `⟨y⟩`, a 4-cycle carries twists
`x^K, y^L` for arbitrary `K, L`. Whether a filling with bounded twists always
exists is a question about the coarse geometry of `G_w` relative to its edge
stabilizers (the link, coned off along the edge-stabilizer cosets), not about
`δ_{G_w}` or distortion alone. Under `[G_e : G_σ] < ∞` the link is locally
finite and every twist is bounded; this is the mechanism behind Theorem C.

## 3. Related work to check

Sauer–Weis, *Polynomial homological Dehn functions from non-proper actions*,
arXiv:2606.25897v1 (24 June 2026), abstract only: "a combination theorem for
polynomial Dehn functions, which is reminiscent of a theorem of Brown for
finiteness properties." Per p. 3 of Llosa Isenrich–Weis, it bounds homological
Dehn functions polynomially for complexes of groups when the filling functions
of the complex, the homological Dehn functions of all cell stabilizers and the
distortion of cell stabilizers are polynomial. Whether it needs finite-index
faces decides whether the homological analogue of (UB) is already known in
general. Read its main theorem before any novelty claim.

## 4. Sharpest next targets

1. Bounded-twist fillings: prove that every loop in `X̂` of length `n` has a
   projection filling of area `≼ δ_X(n)` whose detours are bounded by a
   function of `n`, the distortion of the edge stabilizers and a relative
   coarse invariant of `(G_v; edge stabilizers)`. This is the missing datum.
   It is bounded under finite index and linear for products of trees (part 1,
   §3).
2. Counterexample search: square complexes of groups over a single square with
   trivial face group, vertex groups `ℤ²` or free, and cyclic edge groups with
   trivial pairwise intersections. The development is a CAT(0) square complex
   (links of girth ≥ 4), so `δ_X ≼ n²`, and the vertex groups are 2-dimensional
   with quadratic Dehn functions. What remains is to find identifications for
   which `G` has superpolynomial Dehn function while the vertex groups stay
   polynomially distorted, i.e. unavoidable large twists.
