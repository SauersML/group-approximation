---
rg: 2
id: kernel-block-realizers-re-edit-proof
kind: route
title: Three-point re-edits of product generators make each block group primitive with a 3-cycle, hence alternating, and invariant blocks then realize everything
target: kernel-block-realizers-exist-after-small-re-edit
requires:
  - kun-expander-decomposition-formalized
  - kazhdan-kernel-blocks-invariant-under-sofic-invisible-quotient
---

Notation as in the target. Enlarging `S` changes nothing below, so assume
`S = {s_1, ..., s_m}` with `m >= 2` and `1 not in S`.

1. **Kun's blocks.** Fix an edit for `S` (`kun-expander-decomposition-formalized`)
   with edited permutations `s~` and blocks `B` of Cheeger constant at least `h`.
   Let `rho_n` be the edited sofic radius of
   `inner-realizers-are-at-least-half-the-sofic-radius`. For fixed `r`,
   `|{rho_n < r}| = o(|X_n|)` (step 6 of `inner-realizer-length-radius-proof`).
2. **Few blocks.** In a block of size `k`, two distinct elements of `N` of length
   at most `k` reach the same point from any `x`, because the ball of radius `k`
   in the infinite group `N` has more than `k` elements. So every point of `B` has
   `rho_n < k`, and blocks of size at most `R` carry `o(|X_n|)` points. Hence the
   number of blocks is at most `|X_n|/R + o(|X_n|)` for every `R`, i.e.
   `o(|X_n|)`. Likewise, blocks containing no point with `rho_n >= 1` carry
   `o(|X_n|)` points.
3. **The re-edit.** For `i < m` let `t_i = s_i s_(i+1) in N`, and
   `S+ = S ∪ {t_i^(±1)}`. On a block `B` containing a point `a` with
   `rho_n(a) >= 1`, the points `a, s~_1 a, ..., s~_m a` are distinct, since
   distinct elements of `S ∪ {1}` are distinct in `N`. Put
   `tau_(i,B) = (a, s~_i a, s~_(i+1) a)`, a 3-cycle in `Sym(B)`. Define `t~_i` as
   `s~_i s~_(i+1) tau_(i,B)` on such blocks and `s~_i s~_(i+1)` elsewhere, with
   `t~_i^-1` its inverse.
   - `t~_i` agrees with `s~_i s~_(i+1)` off `3` points per block, hence off
     `o(|X_n|)` points by step 2. It agrees with `sigma_n(t_i)` off `o(|X_n|)`
     points.
   - `t~_i` preserves every block, so the blocks are unchanged. Adding edges does
     not lower the Cheeger constant.
4. **Primitivity.** Fix such a block with `|B| >= 3`. `Pi+_B` contains
   `Pi_B = <s~|_B : s in S>`, which is transitive, and it contains
   `tau_(i,B) = (s~_i s~_(i+1))^-1 t~_i`. Let `Sigma` be a `Pi+_B`-invariant
   partition of `B` into parts of equal size `k`, `2 <= k < |B|`.
   - A 3-cycle `(a b c)` preserving `Sigma` has `a, b, c` in one part. Otherwise
     say `a, b` lie in different parts `P_a != P_b`. Then `tau(P_a) = P_b`, but
     `P_a` contains a point `d != a`, and `tau(d)` is `d` (if `d != c`) or `a`
     (if `d = c`), which lies in `P_a`, a contradiction.
   - Applying this to every `tau_(i,B)` puts `a, s~_1 a, ..., s~_m a` into one part
     `P`. For each `s in S`, `s~ P` is a part containing `s~ a in P`, so `s~ P = P`.
     Then `P` is `Pi_B`-invariant, hence `P = B` by transitivity, a contradiction.

   So `Pi+_B` is primitive.
5. **Jordan's theorem.** A primitive permutation group containing a 3-cycle
   contains the alternating group (C. Jordan, 1873; see Dixon--Mortimer,
   *Permutation Groups*, Section 3.3). So `Pi+_B >= Alt(B)`. By step 2 and step 3 this holds
   on all but `o(|X_n|)` points, which is item 1.
6. **Realizing an element.** Fix `g in G` and `eps > 0`. By
   `kazhdan-kernel-blocks-invariant-under-sofic-invisible-quotient`, the blocks
   with `|sigma_n(g) B Δ B| > eps|B|` carry `o(|X_n|)` points. On any other block,
   `sigma_n(g)` restricts to an injection from `B cap sigma_n(g)^-1 B`, which has
   at least `(1 - eps)|B|` points, into `B`. Extend it to `p in Sym(B)`. If `p` is
   odd, compose with a transposition. The result lies in `Alt(B) <= Pi+_B` and
   agrees with `sigma_n(g)` on at least `(1 - eps)|B| - 2` points of `B`.
7. **Diagonalization.** Blocks of size at most `R` carry `o(|X_n|)` points (step 2),
   and `eps` is arbitrary. So along `U` a choice `eps_n -> 0` gives block-preserving
   `p_n` in `prod_B Pi+_B` with `sigma_n(g) = p_n` off `o(|X_n|)` points, which is
   item 2. ∎
