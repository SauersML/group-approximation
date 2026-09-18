---
rg: 2
id: one-mod-k-partition-posets-are-highly-connected-proof
kind: route
title: Check total semimodularity by hand, then import Björner–Wachs to get a recursive atom ordering, CL-shellability and a wedge of top-dimensional spheres
target: one-mod-k-partition-posets-are-highly-connected
requires: []
---

This is a citation import plus an elementary check.

**Source.** M. L. Wachs, *Poset Topology: Tools and Applications*, IAS/Park City lecture notes, arXiv:math/0602226v2
(dated 11 Feb 2006). The PDF was read 2026-09-18 and its text extracted with `pypdf`. Quotations are verbatim up to
typesetting; `P̂` means `P` with a bottom `0̂` and a top `1̂` adjoined, and `P̄` means the proper part.

**Imported statements.**

- (W1) Semimodularity, §4.2: "A bounded poset P is said to be semimodular if for all u,v ∈ P that cover some x ∈ P,
  there is an element y ∈ P that covers both u and v. [...] A poset is said to be totally semimodular if every closed
  interval is semimodular."
- (W2) Theorem 4.2.3 (Björner and Wachs [38]): "Every ordering of the atoms of a totally semimodular poset is a
  recursive atom ordering."
- (W3) Theorem 4.2.2 (Björner and Wachs [38, 40]): "A bounded poset P is CL-shellable if and only if P admits a
  recursive atom ordering."
- (W4) Section 3.3, after Definition 3.3.1: "All the consequences of EL-shellability discussed in Section 3.2 are also
  consequences of the more general CL-shellability."
- (W5) Theorem 3.2.4 (Björner and Wachs [40]), in Section 3.2: "Suppose P is a poset for which P̂ admits an
  EL-labeling. Then P has the homotopy type of a wedge of spheres, where the number of i-spheres is the number of
  decreasing maximal (i + 2)-chains of P̂."
- (W6) Section 3.4: "Let P be a bounded poset. For x ∈ P, define the rank, r(x) := l([0̂, x]). For R ⊆ [l(P) − 1],
  define the rank-selected subposet P_R := {x ∈ P : r(x) ∈ R}."
  - Theorem 3.4.1 (Björner and Wachs [38]): "Suppose P is pure and CL-shellable. Let R ⊆ [l(P) − 1]. Then P̂_R is also
    CL-shellable, and hence P_R has the homotopy type of a wedge of (|R|−1)-spheres."
- Cross-checks. These are not needed for the derivation.
  - (3.2.1) for `Π_n`: "We conclude that the homotopy type of Π̄_n is given by Π̄_n ≃ ⋁_{(n−1)!} S^{n−3}".
  - Example 4.3.5 for the odd block size lattice, which is `k = 2`: "The odd block size partition poset is totally
    semimodular; so any atom ordering is a recursive atom ordering. [...] We conclude that Π̄^{odd}_{2n+1} has the
    homotopy type of a wedge of [...] spheres of dimension n − 2."
  - Exercise 4.3.6, for general `k`, with Wachs's `d` equal to our `k`:
    - "(b) Show that Π^{1 mod d}_{nd+1} admits a recursive atom ordering."
    - "(e) Show that Π̄^{1 mod d}_{nd+1} has the homotopy type of a wedge of c_n spheres of dimension n−2".
  - Remark 4.3.7: "The recursive atom ordering for the 1 mod d partition lattice (Example 4.3.5 and Exercise 4.3.6 (b))
    is due to Björner (see [54] and [38])".
    - [38] is Björner–Wachs, *On lexicographically shellable posets*, Trans. AMS 277 (1983).
    - [54] is Calderbank–Hanlon–Robinson, Proc. LMS (3) 53 (1986).

**Certificate boundary.** Wachs does not prove W2–W5 in the notes; she cites them. The cross-checks are exercises or
examples. The derivation below uses W1–W5 as published theorems and checks total semimodularity by hand, so it does not
rest on any exercise.

## Derivation

Write `Π = Π^{1 mod k}_n` with `n = tk + 1`, and let `b(x)` be the number of blocks of `x`.

**(a) Blocks and covers.** Every block of `x` has size `≡ 1 mod k`, so `n ≡ b(x) mod k` and `b(x) ≡ 1 mod k`.

Suppose `x < y`. Each block of `y` is a union of `r ≡ 1 mod k` blocks of `x`, since both sizes are `≡ 1`. Merging
`k + 1` of those blocks at a time stays inside `Π` and reaches `y` after `(r − 1)/k` merges per block. So:

- `y` covers `x` iff `y` arises from `x` by merging exactly `k + 1` blocks of `x` into one;
- `Π` is graded with rank `(n − b(x))/k`, from `0` to `t`.

This is item 1.

**(b) `Π` is semimodular.** Let `u ≠ v` both cover `z`: `u` merges a set `S` of `k + 1` blocks of `z`, and `v` merges a
set `T` of `k + 1` blocks of `z`. Let `j = |S ∩ T|`, so `0 <= j <= k`.

- **Case `j = 0`.** Let `w` merge `S` and `T` separately. Then `w` covers `u`, by merging the `k + 1` blocks of `T`, and
  covers `v` likewise.
- **Case `1 <= j <= k`.** We have `|S ∪ T| = 2k + 2 − j >= k + 2`, and `b(z) ≡ 1 mod k` by (a), so `b(z) >= 2k + 1`.
  Choose a set `E` of `j − 1` further blocks of `z` outside `S ∪ T`, and let `w` merge `S ∪ T ∪ E` into one block.
  - That block consists of `2k + 1 ≡ 1 mod k` blocks of `z`, so `w ∈ Π`.
  - From `u`, the move merges the block `∪S` with the `k + 1 − j` blocks of `T \ S` and the `j − 1` blocks of `E`:
    `k + 1` blocks of `u` in all. So `w` covers `u`, and symmetrically `w` covers `v`.

**(c) `Π` is totally semimodular.** Let `x <= y`. Let the blocks of `y` be unions of `r_1, ..., r_s` blocks of `x`,
each `r_i ≡ 1 mod k`. Then `[x, y] ≅ Π^{1 mod k}_{r_1} × ... × Π^{1 mod k}_{r_s}`: an element of the interval is a
choice, for each block of `y`, of a `1 mod k` partition of its `x`-blocks.

A cover in a product changes exactly one coordinate by a cover. Let two covers of `z` in the product be given.

- If they change the same coordinate, apply (b) in that coordinate.
- If they change different coordinates, the element that makes both changes covers both.

So the product is semimodular, which is item 2.

**(d) Homotopy type.**

1. By W2, `Π` admits a recursive atom ordering.
2. By W3, `Π` is CL-shellable.
3. By W4 and W5, the proper part `Π̄` has the homotopy type of a wedge of spheres. The number of `i`-spheres is the
   number of decreasing maximal `(i+2)`-chains of `Π = (Π̄)^`.
4. By (a), every maximal chain of `Π` has length `t`. So only `i = t − 2` occurs.
5. A wedge of `(t−2)`-spheres, possibly empty, is `(t−3)`-connected.

This is item 3.

**(e) Rank selection.**

- `Π` is pure by (a) and CL-shellable by (d).
- Apply W6 with `R = {1, ..., s} ⊆ [t − 1]`. Then `Π_R` has the homotopy type of a wedge of `(s−1)`-spheres, so it is
  `(s−2)`-connected.
- By (a), rank `r` means `n − rk` blocks.

This is item 4. ∎

For `k = 1` this recovers (3.2.1). For `k = 2` it recovers Example 4.3.5, with the same dimension, `n − 2` in Wachs's
indexing.
