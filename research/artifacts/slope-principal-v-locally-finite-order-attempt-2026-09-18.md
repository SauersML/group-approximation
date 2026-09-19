# Attempt: slope-principal sets of `V` are locally of finite order (2026-09-18)

Canonical itinerary bricks are nested; a shrink puts the image on a table cone and a
repeat gives a compression; a recurrence time compares shapes; and the baker map shows
the two comparisons need `n = 1`.

**Status: attempt artifact, not a route.** This was landed on 2026-09-18 as the
direct-proof route `slope-principal-sets-of-v-are-locally-of-finite-order-proof` over
`nv-point-germ-groups-embed-in-zn-by-slope`, and demoted at landing: two of three
referee lenses refuted Step 4 (Theorem B), which asserted that `S × C` is `b`-invariant.
It is not: `σS = S` gives only `b(S × C) ⊆ S × C`, and genuine invariance would force `S`
to be the full shift. Step 4 below has been rewritten with the repair both lenses
recommended (pass to the maximal invariant subset `Y = ⋂_{k >= 0} b^k(S × C)`, the natural
extension of `(S,σ)`); that repair has **not** been refereed. Steps 0-3 (Theorem A) were
found sound by all three lenses. Target claim:
`research/slope-principal-sets-of-v-are-locally-of-finite-order.md`, where the full
referee record is under `## Attempts`.

Notation is Section 0 of `research/artifacts/kazhdan-nv-measure-criterion-2026-09-17.md`.
Full details, including the discussion of what the proof costs at `n >= 2`, are in
`research/artifacts/slope-principal-torsion-rigidity-2026-09-18.md`. The only facts used
are items 1 and 4 of `nv-point-germ-groups-embed-in-zn-by-slope`:

- (item 1) if `g` fixes `x` and `s(g,x) = 0`, then `g` is the identity on a brick
  containing `x`;
- (item 4) if `g` is canonical on a brick `B` with `gB ⊊ B`, and `Z` is closed,
  `g`-invariant and meets `B`, then `g` fixes a point `p ∈ Z ∩ B` with `s(g,p) ≠ 0`.

**Step 0 (itinerary bricks; any `n`).** Fix `g ∈ nV` with table bricks `B_1,…,B_N`.
For `x ∈ C^n` put `y_t = g^t x` and let `i_t` be the index with `y_t ∈ B_{i_t}`. Set
`E_0 = B_{i_0}` and `E_{t+1} = E_t ∩ g^{-(t+1)}(B_{i_{t+1}})`. By induction each `E_t`
is a brick containing `x`, `E_{t+1} ⊆ E_t`, `g^t` is canonical on `E_t`, and
`F_t := g^t(E_t)` is a brick with `y_t ∈ F_t ⊆ B_{i_t}`; moreover
`F_{t+1} = g(F_t) ∩ B_{i_{t+1}}` and `E_{t+1} = E_t` iff `F_{t+1} = g(F_t)`.

*Induction step.* `F_t ⊆ B_{i_t}` and `g` is canonical on `B_{i_t}`, so by the
sub-brick rule `g` is canonical on `F_t` and `g(F_t)` is a brick containing `y_{t+1}`.
Two bricks with a common point meet in the brick of coordinatewise maximal shape, so
`F_{t+1}` is a brick containing `y_{t+1}`. `g^{t+1}` is canonical on `E_t` with image
`g(F_t)` (compose charts), so `E_{t+1} = (g^{t+1}|_{E_t})^{-1}(F_{t+1})` is a sub-brick
of `E_t` containing `x`, on which `g^{t+1}` is canonical with image `F_{t+1}`. ∎

Consequently `s(g^t,x) = |E_t| - |F_t|`.

**Step 1 (stabilized domains).** Let `G <= nV`, let `Z` be closed, `G`-invariant and
slope-principal, let `g ∈ G`, let `M ⊆ Z` be `⟨g⟩`-minimal (Zorn) and `x ∈ M`. Suppose
`E_t = E` for all `t >= T`. If `n = 1`, then some `g^τ` is the identity on `E`; in
particular `x` is periodic.

*Proof.* `x` is recurrent, so there is `τ >= max(T,1)` with `y_τ` agreeing with `x` in every
coordinate up to depth `max_i |E|_i`, that is `y_τ ∈ E`. Both `E` and `F_τ = g^τ(E)`
are bricks containing `y_τ`, of shapes `|E|` and `|E| - s(g^τ,x)`. Of two bricks through
a common point, the one of coordinatewise larger shape is contained in the other.
- `s(g^τ,x) <= 0`, `≠ 0`: then `F_τ ⊊ E`, so `g^τ` is canonical on `E` with
  `g^τ(E) ⊊ E`, and `E ∩ Z ∋ x`. Item 4 gives `p ∈ Z ∩ E` with `g^τ p = p` and
  `s(g^τ,p) ≠ 0`, contradicting slope-principality (`g^τ ∈ G`).
- `s(g^τ,x) >= 0`, `≠ 0`: then `E ⊊ F_τ`, and `g^{-τ}` is canonical on `F_τ` with image
  `E ⊊ F_τ`, and `F_τ ∩ Z ∋ y_τ`. Item 4 gives `p ∈ Z ∩ F_τ` fixed by `g^{-τ}` with
  `s(g^{-τ},p) ≠ 0`; the cocycle identity at `g^{-τ}g^τ` and `g^τ p = p` give
  `s(g^τ,p) = -s(g^{-τ},p) ≠ 0`: the same contradiction.
- `s(g^τ,x) = 0`: then `F_τ = E`, so `g^τ ∘ φ_E = φ_E` and `g^τ` is the identity on `E`.
For `n = 1` a nonzero element of `Z` has a sign, so these three cases are exhaustive.
(For `n >= 2` the remaining case is a slope with coordinates of both signs, where `E`
and `F_τ` are not nested and no compression is produced.) ∎

**Step 2 (shrinking domains, `n = 1`).** With the hypotheses of Step 1 and `n = 1`: for
every `x ∈ Z` the sequence `(E_t)` stabilizes.

*Proof.* Suppose not, and call `τ >= 1` a shrink time if `E_τ ⊊ E_{τ-1}`; there are
infinitely many. By Step 0, `E_τ ⊊ E_{τ-1}` iff `F_τ = g(F_{τ-1}) ∩ B_{i_τ}` is a proper
subset of `g(F_{τ-1})`. For `n = 1` bricks are cones, and two cones that meet are
nested, so this forces `B_{i_τ} ⊊ g(F_{τ-1})` and hence `F_τ = B_{i_τ}`: at every shrink
time the image brick is one of the `N` table cones. Choose shrink times `τ < τ'` with
`i_τ = i_{τ'} = i`, so `F_τ = F_{τ'} = B_i`. Since `E_{τ'} ⊊ E_{τ'-1} ⊆ E_τ` and `g^τ`
is canonical on `E_τ`, the set `P := g^τ(E_{τ'})` is a brick with `P ⊊ B_i`. Both `g^τ`
and `g^{τ'}` are canonical on `E_{τ'}`, so `h := g^{τ'-τ}` is canonical on `P` with
`h(P) = F_{τ'} = B_i`; equivalently `h^{-1}` is canonical on `B_i` with
`h^{-1}(B_i) = P ⊊ B_i`. As `B_i ∩ Z ∋ y_τ`, item 4 gives `p ∈ Z ∩ B_i` fixed by
`h^{-1}`, hence by `h ∈ G`, with `s(h^{-1},p) ≠ 0`, so `s(h,p) ≠ 0` by the cocycle
identity: this contradicts slope-principality. ∎

**Step 3 (Theorem A).** Let `n = 1`, `g ∈ G`, and
`P_Z = {z ∈ Z : g^m z = z for some m >= 1}`.
- If `z ∈ P_Z` with `g^m z = z`, then `g^m ∈ G` fixes `z ∈ Z`, so `s(g^m,z) = 0` by
  slope-principality and `g^m` is the identity on a brick `B_z ∋ z` by item 1. Hence
  `B_z ∩ Z ⊆ P_Z` and `P_Z` is relatively open in `Z`.
- If `Z' := Z \ P_Z` were nonempty it would be closed, `g`-invariant and contained in
  `Z`, hence slope-principal; a `⟨g⟩`-minimal `M ⊆ Z'` and `x ∈ M` would have a
  stabilizing canonical domain sequence by Step 2 and would then be periodic by Step 1,
  contradicting `x ∉ P_Z`. So `Z = P_Z`.
- The bricks `B_z` cover the compact set `Z`; take a finite subcover `B_{z_1},…,B_{z_r}`
  with exponents `m_1,…,m_r`, and put `q = lcm(m_j)`, `W = ⋃_j B_{z_j}`. Then `W` is
  clopen, `W ⊇ Z` and `g^q|_W = id`. ∎

**Step 4 (Theorem B).** `b(0w,y) = (w,0y)`, `b(1w,y) = (w,1y)` has table
`[0]×C, [1]×C -> C×[0], C×[1]`, so `b ∈ 2V` and `s(b,·) = (1,-1)`. By induction
`b^k(x,y) = (σ^k x, x_k…x_1 y)` with `σ` the shift, so `b^k(x,y) = (x,y)` forces
`σ^k x = x`; hence every periodic point of `b` has `σ`-periodic first coordinate. Let
`S ⊆ C` be an aperiodic minimal subshift (Fibonacci/Sturmian, say). Then `S × C` is
closed and disjoint from `Per(b)`, and `σS = S` gives **forward** invariance
`b(S × C) ⊆ S × C` only. It is not `b`-invariant: since
`b(S × C) = {x : 0x ∈ S} × [0] ∪ {x : 1x ∈ S} × [1]`, equality would make every point of
`S` left-special, hence `|L_{k+1}(S)| = 2|L_k(S)|` and `S` the full shift, which is not
aperiodic minimal. (Fibonacci: `11` is not a factor, so for `u ∈ S` starting with `1`,
`(u,1y) ∈ S × C` while `b^{-1}(u,1y) = (1u,y) ∉ S × C`.)

Pass therefore to the maximal invariant subset

```text
Y := ⋂_{k >= 0} b^k(S × C).
```

The sets `b^k(S × C)` are nonempty compacta, nested decreasing by forward invariance, so
`Y` is nonempty and closed; and since `b` is a homeomorphism,
`b(Y) = ⋂_{k >= 1} b^k(S × C) = Y`. Explicitly
`Y = {(u,v) : (v_k…v_1)u ∈ S for all k >= 0}`, the natural extension of `(S,σ)`: under
`(u,v) ↦ …v_2v_1.u_1u_2…` the map `b` becomes the two-sided shift and `Y` the two-sided
subshift of `S`, whose first-coordinate projection is all of `S` because every one-sided
ray in the language of a two-sided subshift extends to the left.

`Y ⊆ S × C` is disjoint from `Per(b)`. A `⟨b⟩`-minimal `M ⊆ Y` exists by Zorn applied to
the nonempty closed `K ⊆ Y` with `b(K) = K`, a poset containing `Y` itself. No `b^m`,
`m ≠ 0`, fixes a point of `M`, so `M` is slope-principal for `⟨b⟩` vacuously, while
`b|_M` has infinite order because `σ|_S` does. So the conclusion of Theorem A fails for
`n = 2`, and for every `n >= 2` by taking `b × id_{C^{n-2}}` and `M × C^{n-2}`. ∎

**Corollaries.** Corollary 1 of the target is Step 3 plus item 1 (principality) and the
identity `Σ_{j<q} s(g,g^j z) = s(g^q,z) = 0` from the cocycle identity. Corollary 2 is
Theorem A plus the two standard facts that an amenable group acting on a compact space
has an invariant probability measure and that a locally finite group is amenable.
