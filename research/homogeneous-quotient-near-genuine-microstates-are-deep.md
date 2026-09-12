---
rg: 2
id: homogeneous-quotient-near-genuine-microstates-are-deep
kind: claim
title: Near-genuine microstates of the homogeneous-quotient crossed product are deep flat congruence towers
distinct_from:
  homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse: that is the leak theorem and its conditional consequences; this constrains the FORMAT of any hypothetical microstate sequence of the same algebra on the exact face, with no embeddability assumed or concluded.
  sl3-homogeneous-quotient-crossed-product-is-connes-embeddable: that is the open embeddability question; this is an unconditional structure theorem about any microstates it would have.
  fixed-shift-invariance-does-not-force-flat-profile: that refutes an inference from shift invariance to a flat level profile for the coset-wreath collapse lane; this PROVES a flat-profile constraint from imprimitivity plus one intertwining unitary, for the homogeneous quotient, with explicit constants.
---

**THEOREM (established here; proof in
`homogeneous-quotient-deep-tower-proof`, with the sharper orthogonal form in
`orthogonal-kazhdan-powers-have-quadratic-depth-loss`).**  Let `n = 3`, `p` a prime,
`A = SL_3(Z[1/p])`, `C = SL_3(Z)`, `h = diag(p,1,1/p)`,
`C_0 = C cap h^-1 C h`, and let `M = L^infinity(X) rtimes A` be the
crossed product of `homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse`
(`X = SL_3(Q_p)/Lambda'`, `r` orbits of `K = SL_3(Z_p)`).  Fix finite
generating sets `S_C` of `C` and `S_0` of `C_0`, with Kazhdan constants
`kappa`, `kappa_0`, and for `j >= 0` the finite `C`-set
`Y_j = K \ X` of level-`j` congruence cells (`|Y_j| = r |SL_3(Z/p^j)|`).

Suppose a finite-dimensional unitary microstate `(rho, {e_y}_(y in Y_(j+1)))`
of `M` on `C^d` (the `e_y` orthogonal projections summing to `1`) has
defect at most `epsilon` on `S_C`, `S_0`, `h` and the cells `Y_(j+1)`:
relator defect of the presentation of `A` on those generators, covariance
defect `||rho(c) e_y rho(c)^* - e_(cy)||_2 <= epsilon` for `c in S_C`, and
`||rho(h) e_y rho(h)^* - sum_(y' subset h(y)) e_(y')||_2 <= epsilon`; and
that its restriction to `C` is `epsilon`-close on `S_C` to a genuine
representation `rho'` of `C` on `C^d`, which then factors through
`SL_3(Z/(p^a m'))` with `p` not dividing `m'`.  Write `F(q)` for the
normalized dimension of the `rho'(Gamma(q))`-fixed subspace.  Then:

```text
(DT1)  F(p^(a-k) m')  >=  1 - C_1 k epsilon / kappa_0        for 0 <= k <= a,
(DT2)  F(p^j m')      <=  1 - 1/(8 |Y_(j+1)|) + C_2 |Y_(j+1)| epsilon / kappa,
(DT3)  a  >=  j + (kappa_0 / (C_1 epsilon)) . (1/(8|Y_(j+1)|) - C_2 |Y_(j+1)| epsilon/kappa),
```

with `C_1 = 8 |S|` for a fixed finite set `S` of signed permutation matrices
and `C_2` absolute.  In words: the genuine part must be a **flat tower** --
the average weight per congruence level over any top segment of levels is
at most `C_1 epsilon / kappa_0` -- and its `p`-adic depth satisfies
`a . epsilon >= c_j kappa_0 / C_1` for every fixed `j`, so along any
microstate sequence with defect `epsilon_k -> 0` the depth `a_k -> infinity`
at least like `1/epsilon_k`.  No regular-trace hypothesis is used.

In fact orthogonality of the Kazhdan projection strengthens `(DT1)` and
`(DT3)`: for another absolute constant `C_square`,

```text
(DT1-square)  F(p^(a-k)m') >= 1-C_square k epsilon^2/kappa_0^2,
(DT3-square)  a >= j + (kappa_0^2/(C_square epsilon^2))
                  . (1/(8|Y_(j+1)|)-C_2|Y_(j+1)|epsilon/kappa).
```

Thus the strongest established depth scale is `Omega(epsilon^(-2))`, and
the average top-level weight is `O(epsilon^2)`.  The linear bounds displayed
first remain valid but are no longer sharp.

**Consequences.**
- The exact face of `sl3-homogeneous-quotient-crossed-product-is-connes-embeddable`
  consists only of deep flat towers: prime-to-`p` congruence microstates
  (the face on which `arithmetic-pair-is-not-relatively-embeddable` reduces
  to its one-unitary system) cannot carry the homogeneous action at all,
  and towers of bounded depth, or of depth `o(1/epsilon^2)`, cannot either.
- The sharp generic obstruction is additive in **squared** defect across
  levels: Pythagoras for the one Kazhdan projection and the contraction
  identity for `T^k` cost `C_square epsilon^2/kappa_0^2` per level.  The
  truncated-shift example in `orthogonal-kazhdan-powers-have-quadratic-depth-loss`
  shows this `k epsilon^2` square function is sharp for one intertwiner.
- Nothing here excludes such towers.  Whether a flat tower of depth
  `~ 1/epsilon^2` or greater can be completed to a microstate of `M` (with the
  `h`-covariance of the cells and the relators of `A`) is exactly the open
  content of the exact face; it is the homogeneous-quotient form of the
  flat multi-scale enemy recorded on `coset-wreath-is-hyperlinear`.
