# A brick-local height-3 renormalization of the induced SMART element (lane gq-nv-obstruct, 2026-09-18)

Status: proof claimed, under review by gq-referee-a and gq-referee-b. Numerical validation has been
requested from gq-affq, which has MSI clearance for renormalization searches. If the claim survives,
`renormalizable-thompson-elements-give-baumslag-solitar` gives `BS(1,3) <= 3V`.

Notation follows `research/artifacts/gq-gq-nv-obstruct-smart-odometer.md`.
- `F` is SMART's moving-tape map on `X = Γ^Z × Q`.
- `Y` is gq-affq's clopen set of first configurations of genuine level-0 moves
  (`smart-induced-on-genuine-moves-has-exact-tripling`). These are the initial configurations of the
  `M_x(0)`: `b_2`/`d_2` on a nonzero cell, `p_2` with a nonzero right neighbour, `q_2` with a nonzero
  left neighbour.
- `U = F_Y`. Every level-`k` move contains exactly `3^k` points of `Y`, and they are consecutive in
  `U`-time.
- The canonical chain of every `y ∈ Y` gives digits `i_0(y), i_1(y), …`: the sub-move index at each
  level. `pos_1(y) = i_0(y)`.

## 1. The renormalization

`A = {y ∈ Y : i_0(y) = 0}`: the first `Y`-point of each level-1 move. It is clopen, because `i_0` is
read off radius 2. `Y = A ⊔ UA ⊔ U^2A` and `U^3 A = A`, since each level-1 move has three consecutive
`Y`-points.

**First `Y`-points of level-1 moves** (from the recursions; `d`, `q` are mirrors of `b`, `p`):

| level-1 move | first `Y`-point (tape, head) | target: first `Y`-point of `M_x(0)` | edit `φ` |
|---|---|---|---|
| `M_b(1)` on `s_+ 0 s_*` | `s_+ 0 s_*`, `b_2` on `s_+` | `s_+ s_*`, `b_2` on `s_+` | delete the right neighbour (a `0`) |
| `M_d(1)` on `s_* 0 s_+` | `s_* 0 s_+`, `d_2` on `s_+` | `s_* s_+`, `d_2` on `s_+` | delete the left neighbour (a `0`) |
| `M_p(1)` on `s_* 0 s_+` | `s_* 2 s_+`, `b_2` on the `2` (after `p_2 ▶`, `p_1 0|2 → b_2`) | `s_* s_+`, `p_2` on `s_*` | delete the head cell, head one left, state `p_2` |
| `M_q(1)` on `s_+ 0 s_*` | `s_+ 2 s_*`, `d_2` on the `2` | `s_+ s_*`, `q_2` on `s_*` | delete the head cell, head one right, state `q_2` |

**The rows are locally distinguishable on `A`.** A `b_2`-point of `A` is of type `b` when its right
neighbour is `0` and of type `p` when its right neighbour is nonzero; the head cell is then `2`.
`d_2` mirrors this.

**φ is brick-local.** Use the coding of `smart-level-zero-return-map-factors-onto-3-adic-odometer-proof`:
the first coordinate is `P(q,c_0) D(c_1) ⋯` and the second is `D(c_{-1}) ⋯`. Each edit is a
prefix replacement.
- Deleting the right neighbour is `P(b_2,c_0) D(0) → P(b_2,c_0)` in coordinate 1.
- Deleting the left neighbour is `D(0) → ε` in coordinate 2.
- The `p` row is `P(b_2,2) D(c_1) → P(p_2,c_{-1}) D(c_1)` in coordinate 1 and `D(c_{-1}) → ε` in
  coordinate 2.

These are finitely many cases.

**This corrects one point.** Deleting a cell adjacent to the head is a bounded prefix change. The tail is
re-indexed, exactly as by any prefix replacement `uw ↦ vw` with `|u| ≠ |v|`, and as by every move of
`F` itself. So §4 of `gq-affq-smart-renormalization-search.md` ("a deletion is not brick-local") does not
apply to deletions next to the head.

**φ is a bijection `A → Y`.** The inverse inserts the deleted cell and undoes the head and state change.
The preimage of a start of `M_x(0)` is in `A`:
- its level-0 move has sub-move boundary values that force parent `x` with index 0, by the case table
  of the odometer artifact §2;
- above level 1 its chain reads the same boundary cells as the chain of `z` above level 0.

## 2. The key lemma: one level less, one cell less

Write `content_K(x, s_+, s_*, ρ)` for the domain content (tape and head) of `M_x(K)` at the first
`Y`-point of its `ρ`-th level-1 sub-move, where `ρ = (i_{K-1}, …, i_1)` in base 3. Write
`content_{K-1}(x, s_+, s_*, ρ)` for the content of `M_x(K-1)` at the start of its `ρ`-th level-0 sub-move.

**Lemma.** `φ(content_K(x,s_+,s_*,ρ)) = content_{K-1}(x,s_+,s_*,ρ)` for all `K >= 1`, all types `x`, all
`s_+ ∈ {1,2}`, `s_* ∈ {0,1,2}` and all `ρ`. Here `φ` acts on the 3-cell region of the current level-1
sub-move, and the rest of the domain is kept.

**Proof, by induction on `K`.**
- `K = 1` is the table in §1.
- For `K+1`, use the recursion from `prop:smart-moves`. `M_x(K+1)` is the domain of a sub-move plus one
  extra cell, and the extra cell never changes during sub-moves:
  - for `b` it is the parent's `s_*` on the right;
  - for `p` it is the parent's `s_*` on the left;
  - `d` and `q` are mirrors.
- The `i`-th sub-move is `M_{σ(x)_i}(K)`, with boundary values `β(x, i, s_+, s_*)` that the junction
  steps write, as pairs `(s_+, s_*)` of the sub-move. For `b`: `(s_+, 0)`, then `(1, s_+)`, then
  `(1, s_+)`. For `p`: `(2, s_+)`, then `(2, s_+)`, then `(s_+, 0)`.
- The side of the extra cell and the function `β` do not depend on `K`.
- So `content_{K+1}(x, s_+, s_*, (i, ρ'))` is the extra cell next to
  `content_K(σ(x)_i, β(x, i, s_+, s_*), ρ')`, and `content_K(x, s_+, s_*, (i, ρ'))` is the same extra cell
  next to `content_{K-1}(σ(x)_i, β(x, i, s_+, s_*), ρ')`.
- The induction hypothesis identifies the two sub-domain contents under `φ`. `φ` acts inside the level-1
  sub-move, which lies in the sub-domain. ∎

## 3. The renormalization identity `φ ∘ U^3 = U ∘ φ` on `A`

1. **Where it holds directly.** Let `y ∈ A` be such that `y` and `U^3 y` lie in one level-`K` move `M`
   for some finite `K`.
   - Write `y = [L] content_K(x,s_+,s_*,ρ) [R]`, where `L` and `R` are the tape outside the domain. Then
     `U^3 y = [L] content_K(x,s_+,s_*,ρ+1) [R]`.
   - `φ` deletes one cell inside the domain and leaves both half-tapes beyond the domain unchanged, read
     from the head. By the lemma, `φ(y) = [L] content_{K-1}(x,s_+,s_*,ρ) [R]` and
     `φ(U^3 y) = [L] content_{K-1}(x,s_+,s_*,ρ+1) [R]`.
   - `U` advances `M_x(K-1)` from its `ρ`-th level-0 sub-move to the `(ρ+1)`-th inside the domain,
     without touching `L` or `R`. So `U φ(y) = φ(U^3 y)`.
2. **These points are dense in `A`.**
   - Case (1) fails exactly when every ancestor of `y`'s level-1 move is a last sub-move. Last sub-moves
     are `p` (in `b` or `p` parents) or `q` (in `d` or `q` parents), and the last sub-move of a `p` or `q`
     move is again `p` or `q`. So the chain is all `p` (or all `q`) from level 1 up.
   - For an all-`p` chain, each ancestor has `s_* = 0` (the `p`-parent case of the table), and all share
     the right end cell, with value `v ∈ {1,2}`. So the tape left of the domains is all `0`.
   - Set one far-left cell to `1`, outside a given window. The ancestor whose `s_*` it is then has
     `s_* ≠ 0`. If `v = 2` its parent is `q`, with index 1, not last. If `v = 1` its parent is `b`, with
     index 2, and `b` is never a last sub-move, so the grandparent case is not last.
   - Either way case (1) holds for the perturbed configuration. It keeps the window, so it stays in `A`
     with the same lower chain. The all-`q` case is the mirror image.
   - So case (1) points accumulate at every point of `A`.
3. **Conclusion.** `φ ∘ U^3` and `U ∘ φ` are continuous, so they agree on all of `A`.

## 4. Consequence

- `U ∈ 2V` has infinite order, since it has no periodic points.
- Under the brick-local conjugacy `ψ: Y → C^2`, the pair `(ψA, ψ φ ψ^-1)` is a height-3 renormalization
  in the sense of `renormalizable-thompson-elements-give-baumslag-solitar`, items 1–3.
- That node gives `s = U' × id ∈ 3V` and `u ∈ 3V` with `u s u^-1 = s^3`, where `U' = ψ U ψ^-1`. So
  `BS(1,3) ≅ ⟨s, u⟩ ≤ 3V`.
- It also gives an element of `3V` with logarithmic distortion, `|s^{3^n}| = O(n)`. That improves the
  known `O(log^4 N)` rate (Callard–Salo) to `O(log N)`, in `3V`.
- **Not claimed:** `BS(1,2)`, which would need a binary hierarchy, and anything for `2V` itself.
