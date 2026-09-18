---
rg: 2
id: two-torus-cross-slit-forces-sqrt-d-loss-in-thin-closing-proof
kind: route
target: two-torus-cross-slit-forces-sqrt-d-loss-in-thin-closing
requires:
  - regular-torus-covers-rank-distance-polynomial-in-profile
  - nonabelian-band-rungs-absorb-ordered-charge-product
  - near-exact-tuples-saturate-linear-conversion-defect
title: Coprime torus sizes kill every period, and the merged row of length 2p+1 forces any centralizer rounding to move 4p+2 points
---

Notation as in the claim. Rows of `Tk` are the sets `{(i, j) : i}` for a fixed `j`, so `b0` moves along rows; columns
are the sets with a fixed `i`, and `c0` moves along columns. Both swaps touch only row 0 and column 0 of each torus.
For permutations `f, g`, `rank(P_f - P_g) = rank(I - P_(g^-1 f))`, and for a permutation `W`,
`|supp W|/2 <= rank(P_W - I) = |supp W| - #(cycles of W on supp W) <= |supp W|`.

## 1. Distance and profile

`b = b0 tau` where `tau` swaps `x1` and `x2`. So `rank(b - b0) = rank(P_tau - I) = 1`, and likewise
`rank(c - c0) = 1`. Since `(b0, c0)` commutes, `dist <= 1`. The pair does not commute (for instance
`[b, c]` has two 2-cycles, which `twotorus.py` confirms), so `dist = 1`. By Lemma B of
`near-exact-tuples-saturate-linear-conversion-defect-proof`, rank distance `delta` gives `rho <= 2 delta`, so
`rho <= 2`.

## 2. Trivial periods

Let `pi : Omega -> Z^2/Lambda` satisfy `pi b = pi + e1` and `pi c = pi + e2`. If a word `w` in `b, c` fixes a point
`y`, then `0 = pi(w y) - pi(y) = ab(w) mod Lambda`, where `ab(w)` is the exponent-sum vector.

- Row 1 of `T1` does not meet the swaps, so it is a `b`-cycle of length `p`: `b^p y = y`, and `(p, 0) in Lambda`.
- Row 1 of `T2` is a `b`-cycle of length `p + 1`, so `(p + 1, 0) in Lambda`.
- Hence `(1, 0) in Lambda`. With column 1 of each torus and `c`, also `(0, 1) in Lambda`.

So `Lambda = Z^2`. In the language of `regular-torus-covers-rank-distance-polynomial-in-profile`, the pair is a cover
of the one-square torus `G = Z^2/Z^2` with fibre `Y = Omega`, `m = |Y| = d`, `N = 1` and `lambda_1 = 1`, and of no
other grid torus.

## 3. One-sided cost

**Cycles of `b`.** `b` agrees with `b0` except at `x1, x2`, where the images are exchanged. So the rows `j != 0` of
`T1` are `p - 1` cycles of length `p`, the rows `j != 0` of `T2` are `p` cycles of length `p + 1`, and the two rows 0
merge into one cycle `Z` of length `2p + 1`: exchanging the images of one point on each of two disjoint cycles joins
them into one cycle. Since `2p + 1` differs from `p` and `p + 1`, `Z` is the only cycle of its length.

**The bound.** Let `c'` commute with `b`. Then `c'` maps each `b`-cycle onto a `b`-cycle of the same length, so
`c'(Z) = Z` and `c'(Omega \ Z) = Omega \ Z`.
- *Points of `Z`.* Take `x` in row 0 of `T1`. If `x != x1`, then `c(x) = c0(x)` lies in row 1 of `T1`. If `x = x1`,
  then `c(x1) = c0(x2)` lies in row 1 of `T2`. Neither is in `Z`, because `p >= 2` makes row 1 differ from row 0.
  The same holds on row 0 of `T2`. So `c(x) != c'(x)` for all `2p + 1` points `x in Z`.
- *Preimages of `Z`.* The swapped points `x1, x2` lie in row 0, so `c = c0` on row `p - 1` of `T1` and row `p` of
  `T2`. So `c^-1(Z)` is exactly these `2p + 1` points. They lie outside `Z`, so `c'` maps them outside `Z`, while `c`
  maps them into `Z`. So `c'` and `c` disagree at `2p + 1` more points.

Hence `|supp(c^-1 c')| >= 4p + 2`, and `rank(c' - c) >= 2p + 1`. The statement for `b'` commuting with `c` is the
same with rows and columns exchanged. Finally `d = 2p^2 + 2p + 1`, so `2d = (2p + 1)^2 + 1`. This gives
`sqrt(2d) < 2p + 2`, so `2p + 1 > sqrt(2d) - 1`. QED (3).

The computation finds exactly `4p + 2` as the least number of disagreements for `2 <= p <= 15`, so the count is tight.

## 4. The thin construction is one-sided

By Section 2, Theorem B must use `G` with `N = 1`. There `lambda_1 = 1 < 96 rho^3`, so its proof takes the thin case,
Lemma 6. The base has one face `o`, and the only charged face is `o`, with holonomy conjugate to `[b, c]^(±1)`.
- There is one charged row, so there is no big gap, and the case `p <= 1` of Lemma 6 applies. The band `B` is the
  single face `o`, bordering itself, as that proof says for `lambda_1 = 1`.
- Every charge already lies in `B`, so no walk and no push is made.
- The rung lemma of `nonabelian-band-rungs-absorb-ordered-charge-product` (Theorem 1) then changes only the rungs of
  `B`, and keeps every other edge. A band of one face on the one-square torus has one rung: its edge is a `b`-edge or
  a `c`-edge of `o`, depending on the direction of the core, and the other generator is kept.

So the output `(b'', c'')` has `b'' = b` or `c'' = c`, and by Section 3 its cost is at least `2p + 1`. The same
holds for every closing that changes only rung values, for any rule of choosing them (support-weighted or not),
because the kept generator is untouched. QED (4).

## 5. Remarks

- **Comparison.** `centralizer-rounding-cannot-bound-rank-distance-by-profile` has one-sided lower bounds on a
  cross slit in `(Z/p)^2 x Z/2`. That pair covers `(Z/p)^2` with fibre of size 2, which is thick, and Theorem B then
  gives a bound independent of `p`. The coprime sizes here remove every period, so no base torus rescues the thin
  construction: the cost of that construction exceeds `sqrt(2d) - 1` while `dist = 1`.
- **Two-sided, not equivariant.** The optimal surgery changes one site of each generator, and is not
  equivariant for any grid torus: before it, the only quotient is the one-square torus; after it, `T1` and `T2`
  cover the thick tori `(Z/p)^2` and `(Z/(p+1))^2`. Any repair of the thin case must include such a non-equivariant,
  two-sided step.
- **Growth.** The loss here is `sqrt(d)`, not `d`. Getting a family with loss linear in `d` would need one-sided cost
  proportional to the area, which the merged-cycle argument cannot give with a bounded number of swaps. This is
  not needed for the obstruction.
