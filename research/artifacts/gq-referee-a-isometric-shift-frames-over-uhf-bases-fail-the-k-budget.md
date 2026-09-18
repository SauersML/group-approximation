# Referee report (gq-referee-a, proof-gap lens): isometric shift frames over UHF bases fail the K-budget

**Reviewed:** `isometric-shift-frames-over-uhf-bases-fail-the-k-budget` and its `-proof` (lane gq-infinite-primes,
9c3ed53c2), read on origin/main (2944807e2).

**Verdict: PASS.** Items 1–4 and the calibrations hold, and I found no gap. There are two nits. The paragraph on
multi-type bases is marked heuristic and conditional on (P), and it is not reviewed here.

## The three points the author asked about
- **Item 1 needs only the equivalence of `1` and `p`.**
  - Take `a = s` (`1×k`) and `b = t` (`k×1`). Then `ab = st = 1` and `ba = ts = p`, with `a = s = sp` and
    `b = t = pt`, so `1 ∈ M_1(R)` and `p ∈ M_k(R)` are Murray–von Neumann equivalent.
  - Equivalent idempotents, possibly of different sizes, have the same class in `K_0(R)`.
  - The unital inclusion `B ⊆ R` sends `[p]_B ↦ [p]_R` and `[1_B] ↦ [1_R]`.
  - So `m[p]_B = n[1_B]` gives `(m−n)[1_R] = 0`. Nothing else is used, and no grading. ✓
- **Cancellation for directed unions of `M_n(Q)`.**
  - A unital embedding `M_(n_i)(Q) → M_(n_j)(Q)` makes `Q^(n_j)` a unital `M_(n_i)(Q)`-module, hence
    `≅ (Q^(n_i))^(n_j/n_i)`. So a rank-one idempotent goes to one of rank `n_j/n_i`, and the `K_0` map is
    multiplication by `n_j/n_i`, which is injective (N1).
  - Then each `K_0(B_i) → K_0(B) = colim` is injective. So `[e] = [f]` in `K_0(B)` already holds in `K_0(B_i)`, for
    any `i` with `e, f ∈ M_k(B_i)`: equal rank at that single stage.
  - Over the field `Q`, idempotents of equal rank are equivalent: `e = xy`, `f = yx`, with `x ∈ eMf` and `y ∈ fMe`.
    ✓
- **The unit computation.**
  - `x = x e_11` and `y = e_11 y`, so `sx` and `yt` have only first entries, `u` and `v`.
  - `uv = (sx)(yt) = s(xy)t = spt = (st)^2 = 1`.
  - `vu = (ytsx)_11 = (ypx)_11`. Since `y ∈ e_11 M p`, `yp = y`, so this is `(yx)_11 = (e_11)_11 = 1` (N2).
  - *Intertwining.* `bu = (bsx)_1 = (st·bsx)_1 = (sxy·tbsx)_1 = u·(ytbsx)_11`, using `s = sp = sxy` and that the row
    `sx` is supported in position 1. So `u^(−1)bu = (y(tbs)x)_11`. It lies in `B` when `tBs ⊆ M_k(B)`, because `x`
    and `y` have entries in `B`. ✓
  - *Grading.* `u = Σ_j s_j x_(j1) ∈ R_1` and `v ∈ R_(−1)`. The graded node's hypotheses hold: a `Z`-grading, a
    degree-one unit, and a unital `Q ⊆ B ⊆ R`. ✓

## Other checks
- **Item 2.** `[p] = n/m`, so `m[p] = n[1_B]`, and `r ≠ 1` gives `m ≠ n`. The `K_1` consequence is cited from
  `rational-k1-detection-forces-infinite-order-unit-class`, item 1.
- **Item 4.** `p ≠ 0` since `spt = 1`, so `r > 0`, and items 2 and 3 exhaust `r ∈ Q_(>0)`.
- **The calibrations.**
  - For `L_Q(1,d)`, `Σ s_i t_i = 1` and `t_i s_j = δ_ij` give `p = I_d` and `r = d`.
  - For `U_n ⋊ Z`, `s = u` and `t = u^(−1)` give `p = 1`, `r = 1`. ✓

## Nits
- **N1 (matricial bases).** Add the one-line reason that a unital embedding of matrix algebras over `Q` multiplies
  `K_0` by `n_j/n_i`: the module count above, or Skolem–Noether.
- **N2 (item 3).** In `vu = (ypx)_11 = (yx)_11`, add "since `yp = y`".
