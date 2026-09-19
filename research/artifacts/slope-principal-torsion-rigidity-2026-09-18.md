# Slope-principal invariant sets: torsion rigidity in `V`, and the baker gap in `nV` (2026-09-18)

Lane `e2-w2-nv-kazhdan-halves`, wave `swarm-0917`, role inverter, family symbolic-dynamics.
Target hole: `slope-principal-minimal-sets-of-nv-subgroups-carry-measures`, the `(T)`-free
half of the split of `minimal-sets-of-kazhdan-subgroups-of-nv-carry-invariant-measures`
recorded by lane `e-nv-kazhdan`.

**Summary of what is new.**

1. **Theorem A (`n = 1`, established, elementary).** Let `G <= V` and let `Z ⊆ C` be a
   nonempty closed `G`-invariant set that is *slope-principal* (`s(g,z) = 0` whenever
   `g ∈ G`, `z ∈ Z`, `gz = z`). Then for every `g ∈ G` there is `q >= 1` with `g^q`
   equal to the identity on a clopen neighbourhood of `Z`. In particular the
   restriction `G|_Z` is a torsion group, and every point of `Z` is a periodic point of
   every element of `G`.
2. **Consequence (Burnside reduction).** A counterexample to the `(T)`-free half at
   `n = 1` is exactly a finitely generated `H <= V` whose germ group along a minimal
   `Z` is an **infinite finitely generated torsion group** acting on `Z` without an
   invariant measure, hence non-amenable. So the `n = 1` case of the `(T)`-free half is
   not `(T)`-free-easy: it implies the non-existence of a non-amenable Burnside-type
   group of germs of `V`-elements.
3. **Theorem B (`n >= 2`, explicit).** Theorem A is false for `n >= 2`.
   Brin's baker map `b ∈ 2V` has constant slope `(1,-1)`, its periodic points form a
   countable set, and over any aperiodic minimal subshift `S ⊆ C` the set `S × C` is
   closed and forward `b`-invariant with **no periodic points at all**; its maximal
   invariant subset `Y = ⋂_{k >= 0} b^k(S × C)`, the natural extension of `(S,σ)`, is a
   nonempty closed genuinely `b`-invariant set, hence vacuously slope-principal, on which
   `b` has infinite order. Every `⟨b⟩`-minimal subset of `Y` is a slope-principal minimal
   set with an infinite-order element.
4. **Correction to the split node.** The failure mode "a free group whose minimal set
   has only saddle fixed points" listed in
   `research/slope-principal-minimal-sets-of-nv-subgroups-carry-measures.md` is not a
   failure mode: a saddle has `s ≠ 0`, so a minimal set containing a saddle fixed point
   is not slope-principal. After Theorem A the only surviving shape of a counterexample
   is a minimal set on which every element with a fixed point is locally trivial there,
   and (for `n >= 2`) the interesting sub-case is a minimal set carrying infinite-order
   elements **without periodic points in it**, of baker type.

Notation is Section 0 of `research/artifacts/kazhdan-nv-measure-criterion-2026-09-17.md`:
bricks `[v] ⊆ C^n` of shape `|v| ∈ N^n`, canonical charts, `g` canonical on a brick,
`D_g`, the slope cocycle `s(g,x) = |w| - |w'| ∈ Z^n`, and the rule that if `g` is
canonical on `B ∋ x` of shape `k` then `g(B)` is the brick of shape `k - s(g,x)`
containing `gx`. The only graph input is the established
`nv-point-germ-groups-embed-in-zn-by-slope`, items 1 (zero slope at a fixed point means
locally trivial) and 4 (a canonical self-compression of a brick meeting a closed
invariant set has a fixed point in that set with nonzero slope). No import from outside
the graph is used anywhere below; in particular revealing-pair theory is **not** used.

## 1. Itinerary bricks

Throughout, `g ∈ nV` is fixed with a table whose pieces are the bricks `B_1,…,B_N`
(a partition of `C^n`, `g` canonical on each).

**Lemma 1.** Let `x ∈ C^n`, `y_t = g^t x`, and let `i_t` be the index with
`y_t ∈ B_{i_t}`. Define
`E_0 = B_{i_0}` and `E_{t+1} = E_t ∩ g^{-(t+1)}(B_{i_{t+1}})`.
Then for every `t >= 0`:
- `E_t` is a brick, `x ∈ E_t`, and `E_{t+1} ⊆ E_t`;
- `g^t` is canonical on `E_t`, and `F_t := g^t(E_t)` is a brick with
  `y_t ∈ F_t ⊆ B_{i_t}`;
- `F_{t+1} = g(F_t) ∩ B_{i_{t+1}}`, and `E_{t+1} = E_t` iff `F_{t+1} = g(F_t)`.

*Proof.* Induction. `t = 0`: `E_0 = B_{i_0}` is a brick containing `x`, `g^0 = id` is
canonical on it, `F_0 = B_{i_0}`.

Assume the statement at `t`. Since `F_t ⊆ B_{i_t}` and `g` is canonical on `B_{i_t}`,
the sub-brick rule makes `g` canonical on `F_t`, so `g(F_t)` is a brick; it contains
`y_{t+1}`, as does `B_{i_{t+1}}`. Two bricks with a common point intersect in the brick
whose shape is the coordinatewise maximum of the two shapes, so
`F_{t+1} := g(F_t) ∩ B_{i_{t+1}}` is a brick containing `y_{t+1}`, and
`F_{t+1} ⊆ B_{i_{t+1}}`. The map `g^{t+1}` is canonical on `E_t` with image `g(F_t)`
(compose the charts of `g^t` on `E_t` and of `g` on `F_t`), so
`E_{t+1} = (g^{t+1}|_{E_t})^{-1}(F_{t+1})` is the sub-brick of `E_t` with
`g^{t+1}(E_{t+1}) = F_{t+1}`, on which `g^{t+1}` is canonical; and `x ∈ E_{t+1}`
because `y_{t+1} ∈ F_{t+1}`. The last equivalence holds because `g^{t+1}|_{E_t}` is a
bijection onto `g(F_t)`. ∎

`(E_t)` is the **canonical domain sequence** of `x` and `(F_t)` its image sequence. By
Lemma 1, `s(g^t, x) = |E_t| - |F_t|`.

## 2. Theorem A

**Theorem A.** Let `G <= V` (`n = 1`) and let `Z ⊆ C` be a nonempty closed
`G`-invariant slope-principal set. Then for every `g ∈ G` there are `q >= 1` and a
clopen `W ⊇ Z` with `g^q|_W = id`.

The proof is three steps. Steps 1 and 2 are stated for general `n`, with the one place
that needs `n = 1` marked; Step 3 is where `n = 1` is used a second time.

**Step 1 (stabilized domains; all `n`, except the saddle case).**
Let `M ⊆ Z` be a nonempty closed `⟨g⟩`-invariant set that is minimal for `⟨g⟩` (Zorn),
and let `x ∈ M`. Suppose the canonical domain sequence of `x` stabilizes:
`E_t = E` for all `t >= T`. Then `x` is a periodic point of `g` and some power of `g`
is the identity on a neighbourhood of `x` — unless `n >= 2` and some `s(g^τ,x)` has
coordinates of both signs.

*Proof.* `x` is uniformly recurrent, because `M` is minimal for `⟨g⟩` and compact. Let
`k = |E| ∈ N^n` be the shape of `E` and pick `τ >= T` with `y_τ` agreeing with `x` in
every coordinate up to depth `max_i k_i`; then `y_τ ∈ E`. Both `E` and
`F_τ = g^τ(E)` are bricks containing `y_τ`, of shapes `k` and `k - s(g^τ,x)`.

- If `s(g^τ,x) <= 0` coordinatewise and `≠ 0`, then `F_τ ⊊ E`: `g^τ` is canonical on
  the brick `E`, which meets the closed `g`-invariant set `Z` (it contains `x`), and
  compresses it. By item 4 of `nv-point-germ-groups-embed-in-zn-by-slope`, `g^τ` fixes a
  point `p ∈ Z ∩ E` with `s(g^τ,p) ≠ 0`. This contradicts slope-principality, since
  `g^τ ∈ G`. So this case does not occur.
- If `s(g^τ,x) >= 0` coordinatewise and `≠ 0`, then `E ⊊ F_τ`, and `g^{-τ}` is
  canonical on `F_τ` with image `E ⊊ F_τ`. `F_τ` meets `Z` (it contains `y_τ`), so the
  same item gives a fixed point of `g^{-τ}` in `Z ∩ F_τ` with nonzero slope: again
  impossible.
- If `s(g^τ,x) = 0`, then `F_τ = E` (two bricks of equal shape through `y_τ`), so `g^τ`
  is canonical on `E` with image `E`, that is `g^τ ∘ φ_E = φ_E`, so `g^τ` is the
  identity on `E ∋ x`. In particular `x` is periodic.
- Coordinates of both signs require `n >= 2`. ∎

**Step 2 (shrinking domains; `n = 1`).**
Let `x ∈ Z` and suppose its canonical domain sequence does not stabilize. If `n = 1`
this contradicts slope-principality.

*Proof.* Call `τ >= 1` a *shrink time* if `E_τ ⊊ E_{τ-1}`; by hypothesis there are
infinitely many. By Lemma 1, `E_τ ⊊ E_{τ-1}` iff `F_τ = g(F_{τ-1}) ∩ B_{i_τ}` is a
proper subset of `g(F_{τ-1})`. **Here `n = 1` enters:** for `n = 1` the pieces are
cones, and two cones that meet are nested, so `F_τ ⊊ g(F_{τ-1})` forces
`B_{i_τ} ⊊ g(F_{τ-1})` and therefore `F_τ = B_{i_τ}`. So at every shrink time the image
brick is one of the `N` table pieces.

Pigeonhole: there are shrink times `τ < τ'` with `i_τ = i_{τ'} = i`, hence
`F_τ = F_{τ'} = B_i`. Since `τ'` is a shrink time and `E` is decreasing,
`E_{τ'} ⊆ E_{τ'-1} ⊊ ... ` gives `E_{τ'} ⊊ E_τ`, so
`P := g^τ(E_{τ'}) ⊊ g^τ(E_τ) = B_i`, and `P` is a brick ( `g^τ` is canonical on
`E_τ ⊇ E_{τ'}` ). Both `g^τ` and `g^{τ'}` are canonical on `E_{τ'}`, so
`h := g^{τ'-τ}` is canonical on `P` with `h(P) = F_{τ'} = B_i`; equivalently `h^{-1}`
is canonical on `B_i` with `h^{-1}(B_i) = P ⊊ B_i`. The brick `B_i` meets `Z`
(it contains `y_τ`), so item 4 of `nv-point-germ-groups-embed-in-zn-by-slope` gives a
point `p ∈ Z ∩ B_i` fixed by `h^{-1}`, hence by `h = g^{τ'-τ} ∈ G`, with
`s(h^{-1},p) ≠ 0` and therefore `s(h,p) = -s(h^{-1},hp) ≠ 0`. This contradicts
slope-principality. ∎

**Step 3 (assembling; `n = 1`).**
Let `g ∈ G`. Write `P_Z = {z ∈ Z : g^m z = z for some m >= 1}`.

- *`P_Z` is relatively open in `Z`, with local identities.* If `z ∈ P_Z` has
  `g^m z = z`, then `g^m ∈ G` fixes `z ∈ Z`, so `s(g^m,z) = 0` by slope-principality,
  so by item 1 of `nv-point-germ-groups-embed-in-zn-by-slope` `g^m` is the identity on a
  brick `B_z ∋ z`. Then `B_z ∩ Z ⊆ P_Z`.
- *`P_Z = Z`.* Otherwise `Z' = Z \ P_Z` is a nonempty closed `g`-invariant subset of
  `Z` (it is closed in `Z` by the previous point, and `g`-invariant because `P_Z` is).
  Pick a `⟨g⟩`-minimal `M ⊆ Z'` and `x ∈ M`. By Step 2 (`n = 1`) the canonical domain
  sequence of `x` stabilizes; by Step 1 (`n = 1`, so no saddle case) `x` is periodic —
  contradicting `x ∈ Z'`.
- *Uniformity.* The bricks `B_z`, `z ∈ Z`, cover the compact `Z`; take a finite
  subcover `B_{z_1},…,B_{z_r}` with exponents `m_1,…,m_r`, put `q = lcm(m_j)` and
  `W = ⋃_j B_{z_j}`. Then `g^q|_W = id` and `W ⊇ Z` is clopen. ∎

**Corollaries.**

- `G|_Z` is a torsion group: every `g ∈ G` has finite order on `Z`.
- The germ groupoid of `G ↷ Z` is principal (slope-principality plus item 1), and
  every element of the topological full group it generates coming from `G` has finite
  order. So the groupoid is generated by torsion bisections.
- Since `g^q = id` on a neighbourhood of `Z`, `Σ_{j<q} s(g, g^j z) = 0` for every
  `z ∈ Z`: the slope cocycle has zero sum around every `⟨g⟩`-cycle in `Z`.

## 3. What Theorem A does to the `(T)`-free half at `n = 1`

Suppose `Z` is a minimal slope-principal set for `G <= V` with no `G`-invariant
probability measure. Then:

1. `G|_Z` is not amenable (an amenable group acting on a compact space has an invariant
   probability measure), so `G|_Z` is not locally finite, so some finitely generated
   `H <= G` has infinite image `H|_Z`.
2. By Theorem A, `H|_Z` is an infinite finitely generated **torsion** group. If
   `H = ⟨g_1,…,g_k⟩` with `g_i^{m_i} = id` near `Z`, then `H|_Z` is a torsion quotient
   of `Z/m_1 * … * Z/m_k`.
3. Conversely, any such object would refute the half.

So at `n = 1` the `(T)`-free half is equivalent to: *no infinite finitely generated
torsion group arises as the germ group along a minimal set of a subgroup of `V` and acts
there without an invariant measure.* That is a Burnside-type statement about `V`. It is
recorded as the open claim `locally-torsion-subgroups-of-v-have-measured-minimal-sets`.

**Verdict on the split.** The split `kazhdan-nv-measured-minimal-sets-via-slope-principality`
was proposed with all of `(T)` in the first half and the second half "`(T)`-free, so it
can fail on its own". Theorem A shows the second half is not the cheap half: already at
`n = 1`, where the flagship statement itself is known through
`thompson-v-has-haagerup-property`, the second half implies a Burnside-type theorem
about `V` that the graph does not have. The split is therefore not a reduction in
difficulty at `n = 1`; whether it is one at `n >= 2` depends on Section 4, where the
`n = 1` mechanism provably fails.

## 4. Theorem B: the baker gap at `n >= 2`

**Brin's baker map.** Define `b ∈ 2V` by
`b(0w, y) = (w, 0y)`, `b(1w, y) = (w, 1y)`.
Its table has domain bricks `[0] × C`, `[1] × C` and image bricks `C × [0]`, `C × [1]`,
so `b` is a well-defined element of `2V` with constant slope
`s(b,·) = (1,0) - (0,1) = (1,-1)`: a pure saddle slope.

**Dynamics.** `b^k(x,y) = (σ^k x, x_k x_{k-1} … x_1 y)`, where `σ` is the one-sided
shift. So `b^k(x,y) = (x,y)` forces `σ^k x = x`. Hence

> `Per(b) ⊆ {(x,y) : x is σ-periodic}`, and for each `σ`-periodic `x` of period `k` the
> second coordinate is forced to be `y = (x_k…x_1)^∞`. So `Per(b)` is countable.

**Theorem B.** Let `S ⊆ C` be any aperiodic minimal subshift (for instance the
Fibonacci/Sturmian subshift) and put `Y = ⋂_{k >= 0} b^k(S × C)`. Then `Y` is a nonempty
closed `b`-invariant set (`b(Y) = Y`) containing no periodic point of `b`. Any
`⟨b⟩`-minimal `M ⊆ Y` is therefore a minimal set which is slope-principal for `⟨b⟩`
**vacuously** (no element of `⟨b⟩ \ {1}` fixes a point of `M`), while `b|_M` has infinite
order.

*Correction (2026-09-18, referee lenses 1 and 3).* An earlier version of this section took
`Y = S × C` and called it `b`-invariant on the strength of `σS = S`. That is wrong.
`b(x,y) = (σx, x_1y)` gives
`b(S × C) = {x : 0x ∈ S} × [0] ∪ {x : 1x ∈ S} × [1]`, so `σS = S` yields only the forward
inclusion `b(S × C) ⊆ S × C`; equality would make every point of `S` left-special, hence
`|L_{k+1}(S)| = 2|L_k(S)|`, entropy `log 2` and `S` the full shift — never an aperiodic
minimal subshift. (Fibonacci: `11` is not a factor, so for `u ∈ S` beginning with `1` the
point `(u,1y)` lies in `S × C` while `b^{-1}(u,1y) = (1u,y)` does not.) Passing to the
maximal invariant subset repairs it, and the conclusion is unchanged.

*Proof.* `S × C` is closed and, by `σS = S`, forward `b`-invariant, so the compacta
`b^k(S × C)` are nonempty and nested decreasing and `Y` is nonempty and closed; as `b` is
a homeomorphism, `b(Y) = ⋂_{k >= 1} b^k(S × C) = Y`. Unwinding,
`Y = {(u,v) : (v_k…v_1)u ∈ S for all k >= 0}`: this is the natural extension of `(S,σ)`,
and under the identification `C^2 ≅ {0,1}^Z`, `(u,v) ↦ …v_2v_1.u_1u_2…`, the map `b` is
the two-sided shift and `Y` is the two-sided subshift of `S`, whose projection to the
first coordinate is all of `S`. Since `Y ⊆ S × C` and no `x ∈ S` is `σ`-periodic,
`Y ∩ Per(b) = ∅`. A `⟨b⟩`-minimal subset exists by Zorn applied to the nonempty closed
`K ⊆ Y` with `b(K) = K`, a poset that contains `Y` itself. Slope-principality of `M` for
`⟨b⟩` is the empty condition because no `b^m` (`m ≠ 0`) fixes a point of `M`. `b|_M` has
infinite order since `σ|_S` does. ∎

**Consequences for the method.**

- The conclusion of Theorem A ("every element of `G` has a power that is the identity
  near `Z`") is **false** for `n >= 2`. So the failure of Steps 1 and 2 at `n >= 2` is
  not a gap in the write-up: no repair of the argument can exist.
- The two failure points are exactly the two places marked in Section 2, and the baker
  map realizes both:
  - *Step 1, saddle case.* `s(b^τ, x) = (τ, -τ)` always has coordinates of both signs,
    so the image brick `F_τ` and the domain brick `E` are never nested, and no
    compression is produced.
  - *Step 2, non-comparable bricks.* Bricks form a lattice, not a tree: two bricks can
    meet without being nested, so a strict shrink `F_τ ⊊ g(F_{τ-1})` does not force
    `F_τ = B_{i_τ}`, and the "state" (the overhang of `F_τ` inside `B_{i_τ}`) resets in
    some coordinates only. The state set is finite exactly when `n = 1`.
- This is the same wall as the antichain obstruction recorded by lane `e-nv-kazhdan`
  ("infinitely many bricks of increasing shape can form an antichain, and for `n >= 2`
  Dickson's lemma orders shapes but not positions"), now localized to a single named
  step with an explicit witness.

**Class-kill.** Any proof of the `(T)`-free half for `n >= 2` whose only dynamical input
is the trichotomy "compressing fixed point / saddle / locally trivial" of
`nv-point-germ-groups-embed-in-zn-by-slope` fails: on a baker-type minimal set the
trichotomy is vacuous, because the set contains no fixed points of any element at all,
and yet the group acting can be infinite. Such a proof must control elements with **no
periodic points in `Z`**, which the slope hypothesis does not see.

## 5. The shape of a counterexample after this note

Combining Theorem A, Theorem B and the correction in item 4 of the summary, a
counterexample to `slope-principal-minimal-sets-of-nv-subgroups-carry-measures` is a
finitely generated `G <= nV` with a minimal `Z ⊆ C^n` such that

- no invariant probability measure on `Z` (so `G|_Z` is non-amenable);
- every element with a fixed point in `Z` is the identity near it;
- either `n = 1` and `G|_Z` is an infinite finitely generated torsion group
  (Burnside-type), or `n >= 2` and `G` contains elements of baker type acting on `Z`
  with **no periodic points in `Z`**;
- all slopes are unbounded along every orbit
  (`bounded-slope-at-one-point-puts-nv-minimal-set-in-u-k`).

The `n >= 2` branch is the live one, and it suggests the concrete first experiment:
take the group generated by the baker map `b` and prefix permutations that preserve an
aperiodic minimal subshift in the first coordinate, and decide whether some such group
has a minimal set with no invariant measure. Every element of a group all of whose
slopes are of the form `(k,-k)` preserves the Bernoulli measure of `C^2`, so any
counterexample of this shape must have its minimal set inside a Bernoulli-null set; that
is a concrete test, not an obstruction.

## 6. Honest scope

- Theorem A and Theorem B are proved here in full from the established
  `nv-point-germ-groups-embed-in-zn-by-slope` and elementary facts about bricks. No
  external import is used in them, and no revealing-pair theory: the `n = 1` input is
  only that two cones that meet are nested and that a nonzero integer has a sign. (The
  Burnside reduction of item 2 does use two standard facts outside the graph — an
  amenable group acting on a compact space has an invariant probability measure, and a
  locally finite group is amenable — and Theorem B uses the existence of an aperiodic
  minimal subshift, for which Fibonacci/Sturmian is named but not formally cited.)
- **Referee status (2026-09-18, at landing).** The claim node
  `slope-principal-sets-of-v-are-locally-of-finite-order` was **demoted to OPEN**: two of
  three lenses refuted the node as first written, both at the same place, the false
  `b`-invariance of `S × C` in Theorem B. The correction recorded in Section 4 has been
  applied throughout but has not itself been refereed. Theorem A (Steps 0-3 of the attempt
  artifact `research/artifacts/slope-principal-v-locally-finite-order-attempt-2026-09-18.md`)
  survived all three lenses, including the hypotheses-and-citations lens, which recorded
  *survives* outright.
- The `(T)`-free half is **not** proved and **not** refuted. What is established is a
  rigidity theorem at `n = 1` with its Burnside consequence, and the precise failure of
  that rigidity at `n >= 2` with an explicit witness.
- The `(T)` half `minimal-sets-of-kazhdan-subgroups-of-nv-are-slope-principal` is
  untouched here.
