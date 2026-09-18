---
rg: 2
id: unimodular-maslov-cells-do-not-dissect-mixed-atoms
kind: claim
title: For n = 2 the mixed atom of the unimodular Maslov triangle is not a finite union of unimodular cells, so the Farey dissection property behind tree-pair diagrams fails for the Lagrangian Cantorization
distinct_from:
  unimodular-maslov-cantorization-is-minimal-expansive: that builds the Cantorization from unimodular cells and proves its dynamics; this shows that single cells are not a dissection basis of its clopen algebra.
  lagrangian-thompson-group-is-finitely-presented: that remarks that cells are not rigid (infinite Levi stabilizers) and that mediants form an infinite orbit; this is a different failure, a clopen set that is no finite union of cells at all.
  lagrangian-brin-thompson-group-is-finitely-presented: that is the open finiteness question, and this answers its first test (item 3 of Attempts) negatively; finite presentation itself is not decided.
---

**ESTABLISHED** (lane proof below, not reviewed). No priority is claimed.

## Statement

- **Setting.** Let `n = 2`, let `(e, f)` be the standard frame and `G = span(e_i + f_i)`.
- **The triangle.** The frames `(e, f)`, `(e+f, f)` and `(e, e+f)` are unimodular.
  - In the `(e,f)` chart their cell indices at `S` are `c`, `a + c` and `b + c`.
  - Here `a`, `b` and `c` count the eigenvalues of `S` in `(0,1)`, in `(1,∞)`, and below
    `0`.
- **The mixed atom.** `A = {S : 0 < λ_1 < 1 < λ_2}` is the atom of type `(1,1,0)`. It is
  an element of `𝔅_u`.
- **Claim.** `A ∩ Λ^0` is not a finite union of sets `C_k(M, M') ∩ Λ^0`, over unimodular
  transverse pairs `(M, M')`.
- **Consequence.** Unlike the Farey case `n = 1`, not every clopen subset of `Y_u` is a
  finite disjoint union of single cells.
  - So elements of the Lagrangian Thompson and Brin–Thompson groups do not admit
    "cell-pair diagrams" in the manner of tree-pair diagrams.
  - A Stein–Farley-type argument would have to use atoms of arrangements as its basic
    pieces.
- **Not claimed.** Nothing is claimed about finite presentation.

## Proof

**0. Reduction to walls.**
- Suppose `A ∩ Λ^0 = ∪_i (C^{(i)} ∩ Λ^0)` for finitely many cells.
- Cells are regular open: crossing a wall at a rank-one point changes the index by one,
  so no wall point is interior to the closure of a single cell. `A` is the intersection
  `C_0(e,f) ∩ C_1(e+f,f) ∩ C_1(e,e+f)`, hence regular open. So `C^{(i)} ⊆ A` and
  `cl A = ∪_i cl C^{(i)}`.
- A boundary point `p ∈ ∂A` then lies in `∂C^{(i)}` for some `i`, and `∂C^{(i)}` lies in
  the two walls `Σ(M_i) ∪ Σ(M'_i)`.
- If moreover `p ∈ Σ(G)` avoids the finitely many curves `Σ(M) ∩ Σ(G)` with `M ≠ G`,
  then `G` is a wall of that cell.

**1. Slices of Σ(G).**
- Use the chart of the frame `(e+f, f)`, with coordinate `X = S − I`.
- Generic points of `Σ(G)` are `X = μ v v^T`, with `|v| = 1` and `μ ≠ 0`. Put
  `ℓ = L ∩ G = span(w·(e+f))`, where `w ⊥ v`.
- The reduced plane `ℓ^ω/ℓ` has basis `[v·(e+f)]` and `[v·f]`. Reduced Lagrangian lines
  have slopes:
  - `L_ℓ = μ`, `G_ℓ = 0`, `(L_f)_ℓ = ∞`, `(L_e)_ℓ = −1`;
  - for `M` transverse to `G`, written `M = span(f_i − Σ_j Y_ij (e_j + f_j))` with
    `Y ∈ Sym_2(R)`, the slope of `M_ℓ` is `−1/⟨Yv, v⟩`. This gives `Y = I` for `L_e` and
    `Y = 0` for `L_f`.
- These are direct computations of `(N ∩ ℓ^ω + ℓ)/ℓ`.

**2. The atom on a slice.**
- At `X = μ v v^T`, the eigenvalues of `S` are `1` (on `w`) and `1 + μ` (on `v`).
- So `cl A` meets the slice of `ℓ` in the closed arc `μ ∈ [−1, ∞]`, which passes through
  `0`. The point `μ < −1` gives `S` a negative eigenvalue.
- Both open sides lie in `∂A`:
  - for `μ ∈ (−1, 0)`, the other side is the atom `(2,0,0)`;
  - for `μ > 0`, the other side is `(0,2,0)`.

**3. Traces of cells with wall G.**
- Take a frame `(g, h)` with `L_g = G` and `L_h = M`. Compute the slope in its chart as
  in step 1.
- The closures of its three cells meet the slice of `ℓ` as follows:
  - `cl C_1` meets it in the whole circle;
  - `cl C_0` and `cl C_2` meet it in the two closed arcs between `G_ℓ` and `M_ℓ`.
- The reason is that a rank-one `μ' v v^T` is a limit of positive definite matrices iff
  `μ' ≥ 0`, and a limit of indefinite ones always.
- So by step 2 no `C_1(G, M)` lies in `A`.

**4. Contradiction.**
- By steps 0 and 2, for all but finitely many `ℓ`, the part `μ ∈ (−1, 0)` of the slice
  is covered, up to finitely many points, by traces of cells `C_0(G, M_i)` or
  `C_2(G, M_i)` lying in `A`.
- Each such trace is a closed arc starting at `G_ℓ = 0`. It must stay inside `[−1, ∞]`,
  so on the negative side it is `[(M_i)_ℓ, 0]` with `(M_i)_ℓ ∈ [−1, 0)`.
- Covering `(−1, 0)` therefore forces `(M_i)_ℓ = −1` for some `i`.
- By pigeonhole a single `i` works for infinitely many `ℓ`. Then the quadratic form
  `⟨Y_{M_i} v, v⟩ − |v|^2` vanishes on infinitely many directions, so it is zero. Hence
  `Y_{M_i} = I` and `M_i = L_e`.
- So some cell with walls `{G, L_e}` lies in `A`.
- Those are the cells of the frame `(e, e+f)`, with index `b + c`:
  - `b + c = 0` is the atom `(2,0,0)`;
  - `b + c = 1` is `(1,1,0) ∪ (1,0,1)`, which is strictly larger than `A`;
  - `b + c = 2` contains `(0,0,2)`.
- None of them lies in `A`, which is a contradiction.
- The side `μ > 0` gives a second contradiction in the same way, with `L_f` and the
  frame `(e+f, f)`. ∎

## Remarks

- For `n = 1` the analogous atoms are Farey arcs, which are cells. The obstruction uses
  the rank-one slices of a wall, which exist only for `n ≥ 2`.
- The same slice argument should apply to mixed atoms for every `n ≥ 2`. This is not
  checked here.
