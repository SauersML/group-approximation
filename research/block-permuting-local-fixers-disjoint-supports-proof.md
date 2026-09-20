---
rg: 2
id: block-permuting-local-fixers-disjoint-supports-proof
kind: route
title: Proof that block-permuting local fixers cannot live in a torsion-free group with cyclic centralizers
target: block-permuting-local-fixers-force-disjoint-supports
requires: []
---

Lane proof (bh-scout-bbmz, 09-19), not reviewed. Elementary.

Write `supp(g)` for the set of points `g` moves. Then `supp(g^n) ⊆ supp(g)`.

**(D) Disjoint supports are impossible.** Suppose `f, g ≠ 1` have disjoint supports.
- Then they commute, so `f = z^a` and `g = z^b` with `a, b ≠ 0`.
- So `z^{ab} = f^b = g^a` has support inside `supp(f) ∩ supp(g) = ∅`, hence `z^{ab} = 1`.
- That contradicts torsion-freeness.

**Block preservation.** Let `k = m!`. Each `h_i^k` maps every piece onto itself, is the identity on `W_i`, and is
nontrivial because `Γ` is torsion-free. Commutators and powers of piece-preserving elements are piece-preserving.

**Induction.** We build nontrivial piece-preserving `f_j` that are the identity on `W_1 ∪ … ∪ W_j`. Start with
`f_1 = h_1^k`. Given `f_j`, with `j ≤ m−2`, let `g = h_{j+1}^k` and `c = [f_j, g] = f_j g f_j^{-1} g^{-1}`.
- **`c` is the identity on `W_i` for `i ≤ j`.** For `p ∈ W_i`, `g^{-1}p ∈ W_i` is fixed by `f_j^{-1}`, then `g` returns it
  to `p`, which `f_j` fixes.
- **`c` is the identity on `W_{j+1}`.** For `p ∈ W_{j+1}`, `g^{-1}p = p`, then `f_j^{-1}p ∈ W_{j+1}` is fixed by `g`,
  then `f_j` returns it to `p`.
- **If `c ≠ 1`,** set `f_{j+1} = c`.
- **If `c = 1`,** then `f_j = z^a` and `g = z^b` with `a, b ≠ 0`. Set `f_{j+1} = z^{ab}`.
  - It is the identity on `W_1 ∪ … ∪ W_j`, as `f_j^b`.
  - It is the identity on `W_{j+1}`, as `g^a`.
  - It is piece-preserving and nontrivial.

**End.** `f_{m−1} ≠ 1` is supported in `W_m`, and `h_m ≠ 1` is supported in `C ∖ W_m`. By (D) this is impossible. ∎

## Where the hypothesis bites

- **Torsion is needed.** In `S_3` permuting three cones of `C`, the transpositions satisfy every hypothesis except
  torsion-freeness. Their squares are trivial, so the induction has no nontrivial `f_1`.
- **Piece-permuting is needed.** For `h_i` that map a piece onto a proper sub-piece union, `[f_j, g]` need not be the
  identity on `W_{j+1}`. This is exactly the open case of (COMP).
