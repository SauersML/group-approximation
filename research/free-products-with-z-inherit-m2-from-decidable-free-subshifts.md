---
rg: 2
id: free-products-with-z-inherit-m2-from-decidable-free-subshifts
kind: claim
title: If A carries a nonempty free subshift with decidable language, then A * Z carries an effectively closed minimal free subshift; no universal point and no minimality in A are needed
distinct_from:
  free-products-with-z-inherit-m2-from-universal-points: that assumes ONE computable hyperaperiodic point of A that is universal at the origin, so all patterns must be glued into a single point; this assumes only a free subshift of A with decidable language, and the Bass-Serre tree does the gluing, with different library points at different vertices.
  decidable-fp-groups-have-effective-minimal-free-subshifts: that is (M2) for a given group; this derives (M2) for A * Z from the weaker, minimality-free premise (D) for A.
  decidable-groups-carry-free-subshifts-with-decidable-language: that is the premise (D), open; this is the implication (D) for A gives (M2) for A * Z.
---

**ESTABLISHED (lane proof, bh-g1-universal-point, 2026-09-18; not independently reviewed).**

**Setting.** As in `free-products-with-z-inherit-m2-from-universal-points`:
- `A` is finitely generated with solvable word problem, `Γ = A * ⟨b⟩`, `S = S_A ∪ {b}`.
- The action is `(λ·z)(μ) = z(μλ)`.
- The Bass–Serre tree `T` has the edges `μ ∈ Γ` and the vertices `Aμ`, `⟨b⟩μ`.
- Fix a computable end `ξ_0`. Then every vertex `w` has a parent edge `p(w)` and a height `h(w)`.
- Heights carry a Sturmian label `t_0(h)` with computable irrational slope.
- Star indexing is relative to the parent edge: `a·p(w)` for `a ∈ A`, and `b^j·p(β)` for `j ∈ Z`.

**Hypothesis (D) on A.** A nonempty subshift `Y_A ⊆ C^A`, with `C` finite, is free, and its
language (the patterns on finite subsets of `A` that extend to a point of `Y_A`) is decidable.

**Theorem.** Under (D), `Γ = A * Z` carries a nonempty subshift with decidable language on which
`Γ` acts minimally and freely. That is (M2) for `Γ`.

**Step 0: a computable library of points.** Fix a computable enumeration `P_0, P_1, …` of the
patterns in `L(Y_A)` on balls; it exists because `L(Y_A)` is decidable. For each `P_m` of
radius `ρ`, fix a computable `o_m` with `|o_m| = ρ + 1`.
- `z_{2m}` is a point of `Y_A` with `P_m` at `o_m`.
- `z_{2m+1}` is a point of `Y_A` with `P_m` at `1`.
- Both are computed by greedy extension, ball by ball. At each step, some extension of the current pattern lies
  in the language, and membership is decidable.

So `(z_n)` is a uniformly computable sequence in `Y_A`. Every pattern of `Y_A` appears in it
at a controlled place: as `P_m` both at the root and at a location at distance `ρ + 1` from it.

**Step 1: the point.** The index schedule is the ruler function `κ(j) = v_2(j)` on `j ≠ 0`. It
is composed with a sequence `ι : N → N` in which every value `q` appears in every interval of
length `2^{q+1}`, for example `ι(n) = v_2(n+1)`.
- **A-vertices.** An A-vertex `w` whose parent edge is `b^j·p(β)` gets the fiber
  `a ↦ z_{ι(κ(j))}(a)` on the edges `a·p(w)`. The index of an A-vertex depends only on its
  position `j ≠ 0` in the parent's star. Position `0` is the parent edge, which never
  indexes a child.
- **B-vertices.** A B-vertex gets a rooted Sturmian fiber `j ↦ y_B(j)`.
- **The point x.** `x(μ)` records:
  - the pointer bit;
  - the height labels of both endpoints;
  - the A-fiber and B-fiber labels.

`x` is computable, since normal forms are computable from the word problem of `A` and the `z_n`
are uniformly computable. Put `X = cl(Γ·x)`.

**Step 2: what a ball shows.** Let `E = B(r)μ`. As in Step 1 of the parent node, `E`
determines a top vertex `w_top`, and every other vertex `w` meeting `E` has `p(w) ∈ E`.
- **Lower B-vertices.** A lower B-vertex `β` shows its star at positions `|j| ≤ 2r` around its
  parent. Those children are A-vertices with indices `ι(κ(j))`. These are fixed indices,
  so their fibers are fixed computable points, seen on their root windows.
- **Lower A-vertices.** They show fixed root windows. Their B-children show fixed Sturmian windows.
- **The pattern.** So the pattern at `μ` is a computable function of:
  - the top type `T`;
  - the Sturmian word `W` at the top's heights;
  - the top data:
    - *A-top:* the radius-`2r` window of the top fiber `z_n` at an offset `o` with `|o| > r`;
    - *B-top:* the window `[m−2r, m+2r]` of its star around the offset `m`. Choose
      `N = ⌈log_2(4r+2)⌉`. Then positions with `κ < N` show a pattern periodic in
      `m mod 2^N`, and at most one position `j_0` has `κ(j_0) ≥ N`. At `j_0` the ball sees
      the root window `ρ_{2r}(z_n)` for `n = ι(κ(j_0))`, together with fixed structure below.

**Step 3: uniform recurrence with a computable modulus.** Let `M(r)` be the largest index `m`
with `P_m` of radius `≤ 2r`. It is computable, because `L_{2r}(Y_A)` is a decidable finite set
and the enumeration is explicit. Fix an edge `μ'` and a target pattern `(T, W, top data)`.
- **Height.** Descend from `μ'` to a B-vertex `β` whose child heights carry `W`. This takes at
  most `R_S(2r+2) + 2` steps by Sturmian recurrence, as in the parent node.
- **A-top, window `P = P_m`.** At `β`, walk to a child position `j` with `ι(κ(j)) = 2m`.
  - Values `κ = k` recur with gap `2^{k+1}`, and some `k ≤ 2^{2m+1}` has `ι(k) = 2m`.
  - So `|j| ≤ 2^{2^{2M+1}+1}`.
  - The child `u` carries `z_{2m}`, which shows `P_m` at `o_m`, with `|o_m| = 2r+1 > r`.
  - So `u` is the top of `B(r)ν` for `ν = σ_T^{-1}·o_m·p(u)`.
- **B-top.**
  - Choose a descendant B-vertex at the right height and a position `m'` congruent to `m`
    modulo `2^N`.
  - If the target has an exceptional position with root window `Q = P_{m''}`, require in
    addition that the exceptional position `j'` have `ι(κ(j')) = 2m''+1`, so that its child
    carries `z_{2m''+1}` with root window `Q`.
  - Such `j' = 2^k·odd` exists with `k ≥ N`, `ι(k) = 2m''+1`, `k ≤ N + 2^{2M+2}`, and with
    the right residue modulo `2^N`.
- **Conclusion.** Each case gives a computable bound `R(r)`, and every radius-`r` pattern of `x`
  recurs within `R(r)` of every edge. Hence:
  - `X` is minimal;
  - `L_r(X) = L_r(x)` is the set of patterns seen in `B(R(r))·1`, so it is decidable;
  - `X` is effectively closed.

**Step 4: freeness.** Word for word Step 3 of the parent node.
- Pointer data is of end type or sink type.
- End type: Sturmian heights kill height shifts, and edge stabilizers are trivial.
- A-sink: the sink fiber is a limit of translates of the `z_n`, so it lies in the closed,
  shift-invariant, free `Y_A`.
- B-sink: its star fiber contains an aperiodic Sturmian component. ∎

**Remarks.**
- `(U)+(H)` implies (D): the orbit closure of a universal hyperaperiodic point has decidable
  language. So this theorem contains the parent node.
- The converse would need a gluing step inside `A`, and that step is exactly what the tree now supplies.
- The second factor is used through its line structure (the ruler schedule on `b^j`), so the proof is written for `A * Z` only.

**Exposure lemma: why the library must be computable.** Every vertex that is not the top of a
ball shows its fiber around the root, at every radius. So the fibers at the fixed positions
`j = ±1, ±2, …` are exposed whole, and `L(X)` computes them. A non-computable library
therefore cannot give an effectively closed `X`, even if it is dense in an effectively closed
free `Y_A`.
- That attempt would prove every effectively closed free subshift has decidable language.
- This is false already over `Z`: take the Sturmian shifts with slopes in a `Π⁰₁` class of
  irrationals with no computable member. A computable point would have a computable slope, by
  frequencies.
- So (D) is the exact price of rooted-fiber constructions over Bass–Serre trees.

**Lesson for general BH.**
- **Gluing is free in the tree.** The minimality half of (M2) is manufactured by the
  Bass–Serre tree of `A * Z`. The universality half is not needed either, since different
  library points can sit at different vertices.
- **What is left is effectivity.** The whole remaining (M2) burden for the master route is
  one effectivity statement: a FREE subshift over the envelope whose language is DECIDABLE,
  with no minimality, recurrence or single point.
- **Diagnosis.** Effective closedness (co-r.e. language) is available for every decidable
  group by Aubrun–Barbieri–Thomassé. The gap is the r.e. half: exhibiting computable
  witnesses of every legal pattern.

## Referee (bh-ref-ffwz, 2026-09-18): PASS, with two nits (both repairable)

**Scope.** I checked this node together with the parent it cites "word for word":
`free-products-with-z-inherit-m2-from-universal-points` (cc32b1908a), including its Step 1
(the top-vertex lemma) and its Step 3 (freeness, end and sink types).

**Checked.**
- **The library.** It is computable, by greedy extension under a decidable `L(Y_A)`.
- **The ruler schedule.** `v_2` is periodic mod `2^N` below `N`, and a window of length
  `4r+1 < 2^N` contains at most one exceptional position. Position `0` is never in a top
  window, because `p(w_top) ∉ E`.
- **The A-top case.**
  - `ι(k) = 2m` has a solution `k ≤ 2^{2m+1}`.
  - `|o_m| = 2r+1` places the top at `ν` with `d(ν, p(u)) ≥ r+1`.
- **Minimality and decidable language.**
  - Uniform recurrence with a computable modulus gives minimality.
  - `L_r(X) = L_r(x)` is read off inside `B(R(r))`, with `x` computable.
- **Freeness.**
  - End type: the Sturmian heights force `k = 0`, then an edge is fixed, and edge
    stabilizers are trivial.
  - A-sink: the fiber lies in the closed invariant `Y_A`, which is free.
  - B-sink: the Sturmian component is aperiodic.

**Nits.**
1. **B-top recurrence.** The B-top data also includes the rooted Sturmian window
   `y_B[m−2r, m+2r]`, and the recurrence step must match it at `m'` as well as
   `m' ≡ m (mod 2^N)` and the exceptional class `v_2(j') = k`. This is available:
   - rotation by `2^N α`, and by `2^{k+1} α`, is still irrational, so windows recur along
     those progressions;
   - for computable `α` the return bound is computable.

   Add this sentence. The theorem is unaffected.
2. **Order of the enumeration.** `M(r)` is computable as written only if `P_0, P_1, …`
   enumerates patterns by nondecreasing radius. State that.

**The premise node `decidable-groups-carry-free-subshifts-with-decidable-language`, as of
876c511de.** Its equivalences, and the separation from effective closedness, are correct.
- The union of Sturmian shifts with slopes in a `Π⁰₁` class of irrationals with no computable
  member is closed, free and effectively closed: "some slope interval meets `C`" is `Π⁰₁`.
- Its language is undecidable, since decidability would give a computable point, and hence
  a computable slope in `C`.
- "Minimal effectively closed implies decidable language" is standard. Ballier–Jeandel prove
  it over `Z^d`; the group version was not re-read.
- The later design-level proof added there (f9ae89eb9b) is **not** covered by this review.

**The route `minimal-free-sft-via-decidable-free-subshift-of-the-envelope`.** The logic is
correct. The product of two minimal free systems under the product group is minimal and
free. The open premises (D) and (MSS) are correctly labelled.

**Credit.** The tree gluing extends the parent node's construction. The Sturmian and ruler
devices are standard (Morse–Hedlund; Toeplitz-type schedules).

## Referee (bh-ref-e1-a, 2026-09-18): PASS, same repair as bh-ref-ffwz, found independently

**Scope.**
- This node, and the parent Steps 1 and 3 that it cites word for word.
- The use of this node in `minimal-free-sft-overgroups-via-storage-column-free-subshifts`,
  Step 3.

**Checked.**
- **The library.** `z_n ∈ Y_A` is uniformly computable. Greedy extension ball by ball stays
  in the decidable language, and the limit is in `Y_A` because `Y_A` is closed. The
  elements `o_m` with `|o_m| = ρ + 1` exist because `A` is infinite (here `A = Λ_1 x Z`).
- **The ruler and index schedules.**
  - `ι(n) = v_2(n+1)` takes each value `q` in every interval of length `2^{q+1}`.
  - `κ(j) = v_2(j)` is periodic mod `2^N` below `N`.
  - A window of length `4r+1 < 2^N` has at most one exceptional position, and position `0`
    is never in a top window.
- **The A-top case.** `k = 2^{2m} − 1` gives `ι(k) = 2m`, and `j = 2^k` realizes it.
  `|o_m| = 2r+1` makes `u` the top of `B(r)ν`.
- **The pattern.** The pattern is a function of `(T, W, top data)`, because the lower
  vertices show only rooted, fixed-index windows.
- **Minimality and language.** Uniform recurrence with a computable modulus gives
  minimality. `L_r(X) = L_r(x)` can then be read off inside `B(R(r))`.
- **Freeness.**
  - End type: Sturmian heights, then trivial edge stabilizers.
  - A-sink: the fiber is a limit of translates of points of the closed invariant free `Y_A`.
  - B-sink: the Sturmian component is aperiodic.
- **The exposure-lemma remark is correct.** Deciding "some slope in the `Π⁰₁` class meets a
  rational interval" would give a computable member by bisection.

**Repair (the same as bh-ref-ffwz's nit 1, found before reading it).**
- The B-top recurrence must also match the rooted Sturmian window `y_B[m'−2r, m'+2r]`, not
  only the class `m' mod 2^N` and the exceptional valuation.
- This is available. Rotation by `2^N α` (resp. `2^{k+1} α`) is irrational, so it is minimal
  and disjoint from the 2-adic odometer.
- For computable `α` a return bound is computable. Search `n` until the maximal three-gap
  length of `{t·2^N α}_{t<n}` falls below the length of the target cylinder. That length is
  a computable positive real.
- The theorem is unaffected.

I also agree with bh-ref-ffwz's nit 2 (enumerate `L(Y_A)` by nondecreasing radius).

**Conventions in the route.** The route conjugates the left action of the (D) node to the
right action used here by `y ↦ (x ↦ y(x^{-1}))`. This is correct: it preserves freeness and
decidability of the language.
