---
rg: 2
id: two-boundary-fixed-points-block-via-busemann-projection
kind: route
title: Fixing two boundary points bounds the sum of the two Busemann functions, so half their difference quasi-isometrically embeds X in R
target: two-boundary-fixed-points-block-cobounded-qi-h2-actions
requires: []
---

This is a direct proof. It uses the four-point inequality and the definition of `∂X`, but not
properness, the Morse lemma, any topology on `∂X`, or the fact that `X` is geodesic. The only
hyperbolic-plane input, in Step 8, is the hyperboloid model and the existence of geodesic segments in
`H^2`.

**Hypotheses and notation.**
- `X` is a metric space satisfying `(x|z)_w ≥ min{(x|y)_w, (y|z)_w} − δ` for all `x, y, z, w ∈ X`.
- `∂X` is the sequential boundary of `busemann-null-isometries-have-no-boundary-contraction`.
- A group `G` acts on `X` by isometries, and the induced action on `∂X` fixes `ξ ≠ η`.
- Fix `o ∈ X`. Gromov products without a subscript are based at `o`.
- Suppose, for a contradiction, that some orbit `G·o'` is `r`-dense: every `u ∈ X` has some
  `h ∈ G` with `d(u, ho') ≤ r`.

**Step 0: preliminaries.**
- **Base change.** `|(x|y)_w − (x|y)_o| ≤ d(o,w)`, since `d(x,w) − d(x,o)` and `d(y,w) − d(y,o)` both
  lie in `[−d(o,w), d(o,w)]`.
- **Action on the boundary.** For an isometry `h`, `(hy_i|hw_j)_o = (y_i|w_j)_{h^{-1}o}`, which is within
  `d(o, h^{-1}o)` of `(y_i|w_j)_o`.
  - So `h` preserves convergence at infinity and equivalence, and acts on `∂X` by `h[y_i] = [hy_i]`.
  - `h^{-1}` induces the inverse map. So if `hξ = ξ` and `z_i → ξ`, then `h^{-1}z_i → ξ`.
- **Four-point form.** For `x, y, z, t ∈ X`:
  `d(x,y) + d(z,t) ≤ max{d(x,z) + d(y,t), d(y,z) + d(x,t)} + 2δ`.
  - To see this, put `S := d(x,t) + d(y,t) + d(z,t)`.
  - Then `S − 2(x|y)_t = d(x,y) + d(z,t)`, `S − 2(x|z)_t = d(x,z) + d(y,t)` and
    `S − 2(z|y)_t = d(y,z) + d(x,t)`.
  - The displayed inequality is `(x|y)_t ≥ min{(x|z)_t, (z|y)_t} − δ`, multiplied by `−2` and with `S` added.

**Step 1: Busemann functions.**
- Fix `z_i → ξ` and `z'_j → η`. For `u ∈ X` put `a_i(u) := d(u,z_i) − d(o,z_i)` and
  `a'_j(u) := d(u,z'_j) − d(o,z'_j)`. Both lie in `[−d(u,o), d(u,o)]`.
- Define `b_ξ(u) := limsup_i a_i(u)` and `b_η(u) := limsup_j a'_j(u)`.
  - These are finite and 1-Lipschitz, because `|a_i(u) − a_i(v)| ≤ d(u,v)`.
  - Since `a_i(u) = d(u,o) − 2(u|z_i)`, we have `b_ξ(u) = d(u,o) − 2 liminf_i (u|z_i)`.
- Put `f := b_ξ + b_η` and `π := (b_ξ − b_η)/2`.
  - `f` is 2-Lipschitz and `π` is 1-Lipschitz.
  - `b_ξ = f/2 + π` and `b_η = f/2 − π`.

**Step 2: nearly orthogonal index pairs.**
- Since `ξ ≠ η`, the sequences `(z_i)` and `(z'_j)` are not equivalent. So
  `Q_0 := liminf_{i,j→∞} (z_i|z'_j)` is finite. Put `Q := Q_0 + 1`.
- For each `l ≥ 1`, `inf_{i,j ≥ l} (z_i|z'_j) ≤ Q_0`. So there are `i_l, j_l ≥ l` with
  `(z_{i_l}|z'_{j_l}) ≤ Q`, that is,
  `(2.1) d(z_{i_l}, z'_{j_l}) ≥ d(o, z_{i_l}) + d(o, z'_{j_l}) − 2Q`.
- Since `i_l ≥ l`, we have `sup_{l ≥ N} a_{i_l}(u) ≤ sup_{i ≥ N} a_i(u)`, so
  `limsup_l a_{i_l}(u) ≤ b_ξ(u)`. Likewise `limsup_l a'_{j_l}(u) ≤ b_η(u)`.

**Step 3: `f ≥ −2Q` on `X`.**
- For `u ∈ X`, the triangle inequality gives `d(z_{i_l}, z'_{j_l}) ≤ d(z_{i_l}, u) + d(u, z'_{j_l})`.
- With (2.1), `a_{i_l}(u) + a'_{j_l}(u) ≥ −2Q` for every `l`.
- Take `limsup_l`, use `limsup(x_l + y_l) ≤ limsup x_l + limsup y_l` for bounded sequences, and apply
  Step 2. This gives `f(u) ≥ −2Q`.

**Step 4: a distance bound.**
- For `u, v ∈ X`, apply the four-point form to `(x, y, z, t) = (u, v, z_{i_l}, z'_{j_l})`.
- Subtract `d(o,z_{i_l}) + d(o,z'_{j_l})` from both sides and use (2.1):
  `d(u,v) ≤ max{a_{i_l}(u) + a'_{j_l}(v), a_{i_l}(v) + a'_{j_l}(u)} + 2Q + 2δ` for every `l`.
- Take `limsup_l`. The limsup of a maximum of two bounded sequences is the maximum of their limsups.
  As in Step 3, the limsup of each sum is at most the sum of the two limsups, and Step 2 bounds these
  by `b_ξ(u) + b_η(v)` and `b_ξ(v) + b_η(u)`. This gives
  `(4.1) d(u,v) ≤ max{b_ξ(u) + b_η(v), b_ξ(v) + b_η(u)} + 2Q + 2δ = (f(u) + f(v))/2 + |π(u) − π(v)| + 2Q + 2δ`.
- The equality holds because `b_ξ(u) + b_η(v) = (f(u) + f(v))/2 + π(u) − π(v)`, and symmetrically in
  `u` and `v`.

**Step 5: inversion estimate.** Let `h` be an isometry with `hξ = ξ`, and put `w := h^{-1}o`. We show
`b_ξ(ho) + b_ξ(w) ≤ 2δ`.
- Put `z''_i := h^{-1}z_i`. By Step 0, `z''_i → ξ`.
- **Spread.** `liminf_i (w|z_i) ≥ limsup_i (w|z''_i) − δ`.
  - Let `T := limsup_i (w|z''_i) ∈ [0, d(w,o)]` and `ε > 0`.
  - `(z''_m)` and `(z_i)` are equivalent, so there is `N` with `(z''_m|z_i) ≥ T` for all `m, i ≥ N`.
  - Pick `m ≥ N` with `(w|z''_m) ≥ T − ε`.
  - For `i ≥ N`, the four-point inequality at `o` gives
    `(w|z_i) ≥ min{(w|z''_m), (z''_m|z_i)} − δ ≥ T − ε − δ`.
  - Let `ε → 0`.
- **The shifted Busemann value.** Applying the isometry `h^{-1}`,
  `d(ho,z_i) − d(o,z_i) = d(o,z''_i) − d(w,z''_i) = 2(w|z''_i) − d(w,o)`.
  So `b_ξ(ho) = 2 limsup_i (w|z''_i) − d(w,o)`.
- **Sum.** By Step 1, `b_ξ(w) = d(w,o) − 2 liminf_i (w|z_i)`. So
  `b_ξ(ho) + b_ξ(h^{-1}o) = 2(limsup_i (w|z''_i) − liminf_i (w|z_i)) ≤ 2δ`.
- The same argument with `(z'_j)` gives the estimate for `η`. Hence `f(ho) + f(h^{-1}o) ≤ 4δ` for every
  `h ∈ G`.

**Step 6: `f` is bounded above.**
- For `h ∈ G`, Steps 3 and 5 give `f(ho) ≤ 4δ − f(h^{-1}o) ≤ 4δ + 2Q`.
- Let `u ∈ X`, and choose `h ∈ G` with `d(u, ho') ≤ r`. Then
  `d(u, ho) ≤ r + d(ho', ho) = r + d(o', o) =: r'`.
- Since `f` is 2-Lipschitz, `f(u) ≤ 2Q + 4δ + 2r' =: B`.

**Step 7: `π` is a quasi-isometric embedding.**
- By (4.1) and Step 6, `d(u,v) ≤ |π(u) − π(v)| + A` with `A := B + 2Q + 2δ`.
- By Step 1, `|π(u) − π(v)| ≤ d(u,v)`.

**Step 8: contradiction with `H^2`.**
1. **The composite.** Since `X` is quasi-isometric to `H^2`, there are `ψ: H^2 → X`, `K ≥ 1` and `C ≥ 0`
   with `(1/K)d(p,q) − C ≤ d(ψp, ψq) ≤ K d(p,q) + C`.
   - Suppose the quasi-isometry is given as `φ: X → H^2`, with constants `(K, C)` and every point of
     `H^2` within `C` of `φ(X)`.
   - Choose `ψ(p)` with `d(φψp, p) ≤ C`. Then `d(ψp,ψq) ≤ K(d(p,q) + 3C)` and
     `d(ψp,ψq) ≥ (d(p,q) − 3C)/K`, so the bounds above hold after enlarging `C`.
   - Put `Ψ := π∘ψ`. By Step 7, `|Ψ(p) − Ψ(q)| ≤ K d(p,q) + C` and `d(p,q) ≤ K(|Ψ(p) − Ψ(q)| + A + C)`.
   - Put `E := K + C` and `M := K(E + A + C)`.
2. **Three far-apart points.** Use the hyperboloid model:
   `H^2 = {x ∈ R^3 : x_0 > 0, x_0^2 − x_1^2 − x_2^2 = 1}`, with `cosh d(x,y) = x_0y_0 − x_1y_1 − x_2y_2`.
   - For `R > 0` put `P_k := (cosh R, sinh R cos(2πk/3), sinh R sin(2πk/3))`, for `k = 1, 2, 3`.
   - For `k ≠ k'`, `cos(2π(k − k')/3) = −1/2`. So `cosh d(P_k,P_{k'}) = cosh^2 R + (1/2)sinh^2 R ≥ cosh R`.
   - Hence the three pairwise distances all equal some `L ≥ R`.
3. **A point near the middle vertex.** Relabel so that `Ψ(P_2)` lies between `Ψ(P_1)` and `Ψ(P_3)`.
   - Let `γ: [0, L] → H^2` be a unit-speed geodesic from `P_1` to `P_3`.
   - The numbers `a_k := Ψ(γ(min{k, L}))`, for `k = 0, …, ⌈L⌉`, start at `Ψ(P_1)` and end at `Ψ(P_3)`.
     Consecutive ones differ by at most `E`.
   - So some `k` has `|a_k − Ψ(P_2)| ≤ E`. Say `Ψ(P_1) ≤ Ψ(P_2) ≤ Ψ(P_3)`; otherwise replace `Ψ` by
     `−Ψ`, which satisfies the same bounds. Take the least `k` with `a_k ≥ Ψ(P_2)`, which exists
     because the last term is `Ψ(P_3)`. Either `k = 0` and `a_0 = Ψ(P_2)`, or
     `a_{k−1} < Ψ(P_2) ≤ a_k ≤ a_{k−1} + E`.
   - Put `q := γ(min{k, L})`. Then `d(q, P_2) ≤ K(E + A + C) = M`.
4. **Lower bound.** Since `q` lies on `γ`, `d(P_1,q) + d(q,P_3) = L`.
   - The triangle inequality gives `L = d(P_1,P_2) ≤ d(P_1,q) + d(q,P_2)` and
     `L = d(P_3,P_2) ≤ d(P_3,q) + d(q,P_2)`.
   - Adding, `d(q,P_2) ≥ L/2 ≥ R/2`.
5. **Conclusion.** Choosing `R > 2M` contradicts item 3. So no `G`-orbit is coarsely dense. ∎

Remark. Steps 3 and 5 replace Manning's theorem (arXiv:2406.12982, Citation 1.12), which the first
intrinsic attempt recorded under this claim needed. Step 4 replaces the Morse lemma used in the first
sketch.
