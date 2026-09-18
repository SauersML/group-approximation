# Slope-distortion bound and the product-tail gate for Kazhdan subgroups of nV

Lane `swarm-0917-w6-w6-re-pull-z-2` (group-rings / transplanter), 2026-09-17.
Target: `minimal-sets-of-kazhdan-subgroups-of-nv-carry-invariant-measures` (stays OPEN).

Notation as in `research/artifacts/kazhdan-nv-measure-criterion-2026-09-17.md`:
`C = {0,1}^ω`, `σ` the shift, `nV` acting on `C^n`, slope cocycle
`s(g,x) ∈ Z^n`, where on a brick `[u_1] × ... × [u_n]` that `g` maps by prefix
replacement onto `[v_1] × ... × [v_n]` we put `s_i(g,x) = |u_i| - |v_i|`.
Cocycle identity: `s(gh,x) = s(g,hx) + s(h,x)`.

## 1. Slope growth is bounded by word length (proved here)

**Lemma A.** Let `K = ⟨S⟩ ≤ nV` with `S` finite and symmetric, and let
`B = max_{h ∈ S} max_x |s(h,x)|_1`. Then `|s(w,x)|_1 ≤ B |w|_S` for all `w ∈ K`,
`x ∈ C^n`.

*Proof.* `B < ∞` because each `h ∈ S` is given by finitely many brick replacements,
so `s(h,·)` takes finitely many values. If `w = h_1 ... h_L` with `h_j ∈ S`, the
cocycle identity gives `s(w,x) = Σ_j s(h_j, h_{j+1} ... h_L x)`, and each term has
`l^1` norm at most `B`. Take `L = |w|_S`. ∎

**Corollary A1.** If `g ∈ K`, `p ≥ 1`, `g^p x = x` and `v = s(g^p,x) ≠ 0`, then
`|g^{pk}|_S ≥ k |v|_1 / B` for all `k ≥ 1`. So `⟨g⟩` is undistorted in `K`.

*Proof.* `g^p x = x` and the cocycle identity give `s(g^{pk},x) = k v`. Apply Lemma A. ∎

**Corollary A2.** If `g ∈ K` is distorted, i.e. `|g^k|_S = o(k)`, then
`max_x |s(g^k,x)|_1 = o(k)`, and `s(g^p,x) = 0` whenever `g^p x = x`.

These statements are elementary. They explain why distorted elements show up in 2V
(Callard–Salo, arXiv 2208.00685, abstract: "higher-dimensional Brin-Thompson groups
mV admit distortion elements") and not in V: such an element must have zero slope at
all of its periodic points.

### Where this route dies for the target

- **Step that fails:** going from "small asymptotic slope for distorted generators"
  to "bounded slope at one point of a minimal set". The latter is the hypothesis of
  `bounded-slope-at-one-point-puts-nv-minimal-set-in-u-k` (lane c-kaznv).
  Lemma A only gives `|s(h,x)| ≤ B|h|_S`, which is linear. Bounded generation by
  distorted elements does not help. In `SL_3(Z)` an element of word length `L` is a
  bounded product of elementary powers `e^{k_j}`, but the `k_j` can be as large as
  `exp(cL)`. The log-distortion bound `|s(e^{k},x)| = O(log k)` then gives `O(L)`
  again, with no gain.
- **Class where the route is empty:** Kazhdan groups all of whose infinite cyclic
  subgroups are undistorted. For those Corollaries A1/A2 give no information.
  (Uniform lattices in `Sp(m,1)` are Gromov hyperbolic. In hyperbolic groups cyclic
  subgroups are quasi-isometrically embedded. This is standard and is only used for
  this scope remark, not imported.) So no proof of the target can rest on distortion
  alone.

## 2. A formal candidate for the product-factorization gate (statement proved; gate OPEN)

`rank-two-prefix-replacement-groups-contain-infinite-kazhdan` says a proof of the target
must use the product factorization, but it describes that factorization only
heuristically. Here is a checkable version.

**Lemma B (coordinate tail witnesses).** Let `π_i : C^n -> C` be the coordinate
projections and `E_t` tail equivalence on `C` (`y E_t z` iff `σ^a y = σ^b z` for some
`a, b ≥ 0`). For `g ∈ nV` and `x ∈ C^n`:
`σ^{|v_i|} π_i(gx) = σ^{|u_i|} π_i(x)`, where `[u] -> [v]` is the brick replacement
used by `g` at `x`. So:

1. the orbit relation of any `K ≤ nV` is contained in `E_t^{×n}`;
2. if `π_i(x)` is not eventually periodic, then the lag `b - a` in
   `σ^a π_i(gx) = σ^b π_i(x)` is unique and equals `s_i(g,x)`. So on the dense
   `G_δ` set `P` of points with no eventually periodic coordinate, `s` is a function
   of the pair `(x, gx)` only;
3. each `s_i` is witnessed by coordinate `i` alone. The lag of coordinate `i` is read
   off from `π_i(x)` and `π_i(gx)` without looking at the other coordinates.

*Proof.* On the brick, `g(x) = (v_1 σ^{|u_1|} x_1, ..., v_n σ^{|u_n|} x_n)`, which gives
the displayed identity and 1. For 2: if `σ^a y = σ^b z` and `σ^{a'} y = σ^{b'} z` with
`b - a ≠ b' - a'`, then `z` is eventually periodic. 3 is immediate from the formula. ∎

**What a Robertson–Steger system has.** Its prefix replacements come with `Z²` shape
offsets. Its boundary groupoid carries a `Z²`-valued lag. So items 1–2, with `E_t^{×n}`
replaced by the rank-two tail relation, hold for `Γ ↷ Ω` as well (heuristic; not
checked in the RS notation). The part that plausibly fails is item 3.

**Gate question (OPEN, not claimed).** For the RS action `Γ ↷ Ω`, are there continuous
maps `π_1, π_2 : Ω -> C` with `π = (π_1, π_2)` injective such that every `γ ∈ Γ`
satisfies `σ^{a_i} π_i(γω) = σ^{b_i} π_i(ω)` with `b_i - a_i` equal to the `i`-th shape
offset, locally constantly in `ω`?

- If the answer is no, item 3 is the invariant every proof of the target must use, and
  this makes the class kill of the rank-two node formal.
- If the answer is yes, then `π` is a topological conjugacy of `Γ ↷ Ω` onto its image
  in `C²`. On that image each `γ` acts coordinatewise by prefix replacements. That is
  most of the way to an embedding of an infinite Kazhdan group into a groupoid of
  germs of `2V`, which would point toward a counterexample to the target.

Either answer changes beliefs, which is why this is recorded as a question. It was not
resolved in this lane.

## 3. Autonomous-coordinate induction (duplicate of c-kaznv; recorded only for the failure step)

If some coordinate is autonomous for `K`, i.e. `π_i(gx)` depends only on `π_i(x)` for
all `g ∈ K`, then:

- `K -> V` through that coordinate has a Kazhdan image, hence a finite image
  (V is Haagerup);
- the kernel lies in the locally constant maps `C -> (n-1)V`, and induction applies.

This is `kazhdan-subgroups-of-nv-fibration-stabilizers-are-finite` (lane c-kaznv,
posted as a LEMMA on the bus). **Failure step:** the very first projection, when no
coordinate (even up to permuting coordinates) is autonomous.

- Example element: the controlled flip `c(x_1,x_2) = (x_1 with its first bit flipped if
  x_2 starts with 0, x_2)`. For `c`, `π_1(cx)` depends on `x_2`.
- A coupled `K` has no `V`-quotient to work with.
- The coupling is exactly what distinguishes nV from a product of copies of V. It is
  the same coupling that Lemma B item 3 does not see, because item 3 constrains lags,
  not the letters that are written.
