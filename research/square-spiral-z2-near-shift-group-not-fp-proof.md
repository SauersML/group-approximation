---
rg: 2
id: square-spiral-z2-near-shift-group-not-fp-proof
kind: route
title: Diagonal line shifts make R_nu metabelian with a one-dimensional character coordinate, and an ascending splitting cannot exhaust it
target: square-spiral-z2-near-shift-group-is-not-finitely-presented
requires:
  - square-spiral-z2-enumeration-passes-the-finite-window-gate
  - fp-groups-without-free-subgroups-split-ascendingly-over-kernels
  - shell-germ-fp-is-an-ascending-hnn-gate
  - shell-germ-group-has-index-two-fiber-product
artifacts:
  - research/artifacts/hl-bh-universal-2-2026-09-13.md
  - research/artifacts/hl-bh-universal-2-2026-09-13/spiral_vectors.py
  - research/artifacts/hl-bh-universal-2-2026-09-13/vectors.json
---

Notation from `square-spiral-z2-enumeration-passes-the-finite-window-gate`: `a = x - y`,
`b = x + y`, and `sigma` is the four-piece translation whose piece is decided by the signs of
`a` and `b`. All equalities of maps hold at all but finitely many points. Composition is
right to left.

**Step 1. How words act far along a half-line.**
- A letter `L_h` changes `a` by `h1 - h2`. The letter `sigma` changes `a` by `-1` wherever
  `b > 0`: on `R` it adds `e2` and on `T` it subtracts `e1`. So `sigma^-1` changes `a` by
  `+1` there.
- Fix a word `w` of length `m` and a half-line `{a = c, b > 0}`. At points of it with
  `b > 4m`, every chain point has `b > 0`. The piece of each chain point depends only on
  `c` and the letters, not on `b`.
- So `w` acts on the far part of this half-line as one translation `v(w, c)`, with
  `a`-component `chi_1(w) = sum of the letter contributions`.
- Two words representing the same near permutation agree at almost all points, so
  `chi_1(w)` depends only on the element. This defines a homomorphism
  `chi_1: R_nu -> Z` with `chi_1(L_e1) = 1`, `chi_1(L_e2) = -1`, `chi_1(sigma) = -1`.

**Step 2. Conjugating line shifts.**
- **Quadrant-I shifts.** Let `delta` be the shift by `+-(1,1)` along
  `{a = c, b > 0}`, and `g` in `R_nu`. By Step 1, `g` maps the far part of this half-line
  onto the far part of `{a = c + chi_1(g), b > 0}` by one translation. So `g delta g^-1` is
  the shift in the same direction along the half-line with offset `c + chi_1(g)`.
- **Other half-lines.** The same argument applies on `{a = c, b < 0}`, `{b = c, a > 0}`
  and `{b = c, a < 0}`, measuring the offset by `a` or `b` and using the sign of the other
  coordinate. Every letter acts on the far part of such a half-line as one translation.
  So conjugation by `L_h` and `sigma^(+-1)` sends a line shift to a line shift, on a
  half-line of the same family and in the same direction.
- **So `D` is normal.** `D` is normalized by the generators of `R_nu`.
- **`D` is abelian.** Shifts along different half-lines have disjoint supports far out.
  Shifts along one half-line are powers of one shift, modulo finitary permutations.
- **The coordinate map.** Define `pi_1: D -> Z[t^(+-1)]` recording the shift amount on each
  quadrant-I half-line `{a = c, b > 0}` as the coefficient of `t^c`, with inward steps `+1`.
  It is a homomorphism, and `pi_1(g delta g^-1) = t^(chi_1(g)) pi_1(delta)`.

**Step 3. `R_nu'` lies in `D`, and `pi_1(R_nu') != 0`.**
- **Generators.** `R_nu'` is the normal closure of the commutators of the generators
  `L_e1, L_e2, sigma`. `[L_e1, L_e2] = 1`, and
  `[sigma, L_h] = sigma L_h sigma^-1 L_h^-1 = L_h delta_1(h) L_h^-1`, with
  `delta_1(h) = L_-h sigma L_h sigma^-1`.
- **`delta_1(h)` is in `D`.** `spiral_vectors.py` (on MSI) compares `sigma L_h sigma^-1`
  with `L_h` on complete rings 60, 61, 90, 91.
  - Every defect is one diagonal step along the diagonal line through the point; the
    `other` list is empty.
  - The pattern is the same on all four rings (`vectors.json`).
  - The invariance argument of Step 4 of `square-spiral-z2-finite-window-gate-proof`,
    applied to these 4-letter words (travel at most 4), makes ring 60 a fundamental domain
    for each strip half beyond the finite central region. Off the strips there are no
    defects.
  - Hence `delta_1(h)` is in `D`.
- **Normal closure.** Since `D` is normal (Step 2), `R_nu' <= D`, and `R_nu` is metabelian.
- **Nonzero coordinate.** `pi_1(delta_1(e1)) = -t^-1` (`vectors.json`, `j=1 h=e1`: entry
  `Q1:-1`, value `-1`). So `pi_1([sigma, L_e1]) = t pi_1(delta_1(e1)) = -1`, which is
  nonzero.
- **The ideal `I`.** `I := pi_1(R_nu')` is an additive subgroup of `Z[t^(+-1)]`. It is
  closed under multiplication by `t^(+-1)`, by conjugating with `L_e1^(+-1)`. So `I` is a
  nonzero ideal, and it contains elements of arbitrarily negative and arbitrarily positive
  degree.

**Step 4. An ascending splitting is impossible.**
- **Setup.** Suppose `R_nu` is finitely presented. It is metabelian, so it contains no free
  subgroup of rank 2. By `fp-groups-without-free-subgroups-split-ascendingly-over-kernels`
  applied to `chi_1`, there are a finitely generated `H <= ker(chi_1)`, an element `u` with
  `chi_1(u) = +-1`, and a sign such that `ker(chi_1) = union_(n >= 0) u^(eps*n) H u^(-eps*n)`.
- **The quotient `G`.** Put `N_1 = R_nu' ∩ ker(pi_1)`, normal in `R_nu` by Step 2. Let
  `G = ker(chi_1)/N_1` and `A = R_nu'/N_1`, so `A ≅ I` via `pi_1`.
  - Elements of `ker(chi_1)` act on `pi_1`-values by `t^0`, so `A` is central in `G`.
  - `G/A` is a subgroup of the abelian group `R_nu/R_nu'`.
  - So `G` is nilpotent of class at most 2.
- **Bounded degrees.** The image `Hbar` of `H` in `G` is a finitely generated nilpotent
  group. Its subgroups are finitely generated (standard, not re-read), so `Hbar ∩ A` is a
  finitely generated abelian group. Its image `J = pi_1(Hbar ∩ A)` is a finitely generated
  subgroup of `I`, so all exponents of elements of `J` lie in some interval `[p, q]`.
- **Exhaustion.** From the splitting, `A = union_n (u^(eps n) Hbar u^(-eps n) ∩ A)`, which
  equals `union_n u^(eps n)(Hbar ∩ A) u^(-eps n)` since `A` is normal. Applying `pi_1`,
  `I = union_(n >= 0) t^(n*eps*chi_1(u)) J`. So every element of `I` has all exponents
  `>= p`, or all `<= q`, depending on the sign of `eps*chi_1(u)`.
- **Contradiction.** This contradicts Step 3. So `R_nu` is not finitely presented.

**Step 5. Consequences.**
- `shell-germ-fp-is-an-ascending-hnn-gate`: `Q` finitely presented implies `R_nu` finitely
  presented. So `Q` is not finitely presented.
- `shell-germ-group-has-index-two-fiber-product`: `Q` and `F_nu` are finitely presented
  together, and `A_1` finitely presented implies `F_nu` finitely presented. So neither
  `F_nu` nor `A_1` is finitely presented for this enumeration.
